import Mathlib
import OAI.Analysis.HardSphere.Geometry.EuclideanTorus
import OAI.Analysis.HardSphere.Allocation.NormalizedNearestSeparated

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter

def centeredCircleLift (L : Length) (x : AddCircle L.val) : ℝ :=
  let t := ((AddCircle.equivIco L.val 0) x).val
  t-(round (L.val⁻¹*t):ℝ)*L.val

lemma centeredCircleLift_coe (L : Length) (x : AddCircle L.val) :
    (centeredCircleLift L x : AddCircle L.val)=x := by
  unfold centeredCircleLift
  rw [AddCircle.coe_sub,←zsmul_eq_mul,AddCircle.coe_zsmul,AddCircle.coe_period,zsmul_zero,sub_zero]
  exact AddCircle.coe_equivIco

lemma centeredCircleLift_abs (L : Length) (x : AddCircle L.val) :
    |centeredCircleLift L x|=‖x‖ := by
  conv_rhs => rw [←(show ((((AddCircle.equivIco L.val 0) x).val):AddCircle L.val)=x from AddCircle.coe_equivIco)]
  exact (AddCircle.norm_eq L.val).symm

def centeredTorusVector (L : Length) (x c : Torus L) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun q ↦ centeredCircleLift L (x q-c q))

lemma centeredTorusVector_norm (L : Length) (x c : Torus L) :
    ‖centeredTorusVector L x c‖=torusDistance L x c := by
  rw [EuclideanSpace.norm_eq]
  unfold torusDistance
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  change ‖centeredCircleLift L (x q-c q)‖^2=dist (x q) (c q)^2
  rw [Real.norm_eq_abs,centeredCircleLift_abs,dist_eq_norm]

lemma centeredTorusVector_coe (L : Length) (x c : Torus L) (q : Fin 3) :
    ((centeredTorusVector L x c q):AddCircle L.val)=x q-c q :=
  centeredCircleLift_coe L _

lemma centeredTorusVector_distance (L : Length) (x y c : Torus L) :
    torusDistance L x y≤‖centeredTorusVector L x c-centeredTorusVector L y c‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold torusDistance
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro q _
  have hcoe : (((centeredTorusVector L x c q-centeredTorusVector L y c q):ℝ):AddCircle L.val)=x q-y q := by
    rw [AddCircle.coe_sub,centeredTorusVector_coe,centeredTorusVector_coe]
    abel
  have hnorm : dist (x q) (y q)≤‖centeredTorusVector L x c q-centeredTorusVector L y c q‖ := by
    rw [dist_eq_norm,←hcoe]
    exact QuotientAddGroup.norm_mk_le_norm
  exact (sq_le_sq₀ dist_nonneg (norm_nonneg _)).mpr hnorm

theorem torus_nearest_incoming_card {ι : Type*} [DecidableEq ι]
    (L : Length) (X : ι→Torus L) (c : Torus L) (I : Finset ι)
    (h0 : ∀ i∈I, X i≠c)
    (hne : ∀ i∈I, ∀ j∈I, i≠j → torusDistance L (X i) c≤torusDistance L (X i) (X j)) :
    I.card≤125 := by
  have hz : ∀ i∈I, centeredTorusVector L (X i) c≠0 := by
    intro i hi he
    apply h0 i hi
    funext q
    have h := centeredTorusVector_coe L (X i) c q
    rw [he] at h
    exact sub_eq_zero.mp (by simpa using h.symm)
  have hsep : ∀ i∈I, ∀ j∈I, i≠j →
      ‖centeredTorusVector L (X i) c‖≤‖centeredTorusVector L (X i) c-centeredTorusVector L (X j) c‖ := by
    intro i hi j hj hij
    rw [centeredTorusVector_norm]
    exact (hne i hi j hj hij).trans (centeredTorusVector_distance L (X i) (X j) c)
  have h := nearest_incoming_card I (fun i ↦ centeredTorusVector L (X i) c) hz hsep
  simpa using h

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

lemma otherLabels_nonempty (i : ι) : (Finset.univ.erase i).Nonempty := by
  obtain ⟨j,hj⟩ := exists_ne i
  exact ⟨j,Finset.mem_erase.mpr ⟨hj,Finset.mem_univ _⟩⟩

lemma nearestLabel_exists (L : Length) (X : ι→Torus L) (i : ι) :
    ∃ j : ι, j≠i ∧ ∀ k : ι, k≠i → torusDistance L (X i) (X j)≤torusDistance L (X i) (X k) := by
  obtain ⟨j,hj,hm⟩ := (Finset.univ.erase i).exists_min_image
    (fun j ↦ torusDistance L (X i) (X j)) (otherLabels_nonempty i)
  exact ⟨j,(Finset.mem_erase.mp hj).1,fun k hk ↦ hm k (Finset.mem_erase.mpr ⟨hk,Finset.mem_univ _⟩)⟩

def nearestLabel (L : Length) (X : ι→Torus L) (i : ι) : ι :=
  Classical.choose (nearestLabel_exists L X i)

lemma nearestLabel_ne (L : Length) (X : ι→Torus L) (i : ι) : nearestLabel L X i≠i :=
  (Classical.choose_spec (nearestLabel_exists L X i)).1

def nearestParticleDistance (L : Length) (X : ι→Torus L) (i : ι) : ℝ :=
  torusDistance L (X i) (X (nearestLabel L X i))

lemma nearestParticleDistance_le (L : Length) (X : ι→Torus L) (i j : ι) (hji : j≠i) :
    nearestParticleDistance L X i≤torusDistance L (X i) (X j) :=
  (Classical.choose_spec (nearestLabel_exists L X i)).2 j hji

lemma nearestParticleDistance_nonneg (L : Length) (X : ι→Torus L) (i : ι) :
    0≤nearestParticleDistance L X i := Real.sqrt_nonneg _

lemma nearestParticleDistance_inf (L : Length) (X : ι→Torus L) (i : ι) :
    nearestParticleDistance L X i=(Finset.univ.erase i).inf' (otherLabels_nonempty i)
      (fun j ↦ torusDistance L (X i) (X j)) := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro j hj
    exact nearestParticleDistance_le L X i j (Finset.mem_erase.mp hj).1
  · exact Finset.inf'_le _ (Finset.mem_erase.mpr ⟨nearestLabel_ne L X i,Finset.mem_univ _⟩)

lemma nearestParticleDistance_continuous (L : Length) (i : ι) :
    Continuous (fun X : ι→Torus L ↦ nearestParticleDistance L X i) := by
  simp_rw [nearestParticleDistance_inf]
  apply Continuous.finset_inf'_apply
  intro j _
  unfold torusDistance
  fun_prop

lemma nearestLabel_fiber_card (L : Length) (X : ι→Torus L) (hX : Function.Injective X) (k : ι) :
    (Finset.univ.filter (fun i ↦ nearestLabel L X i=k)).card≤125 := by
  apply torus_nearest_incoming_card L X (X k)
  · intro i hi
    have hik : i≠k := by
      intro he
      have hm := nearestLabel_ne L X i
      exact hm ((Finset.mem_filter.mp hi).2.trans he.symm)
    exact fun he ↦ hik (hX he)
  · intro i hi j _ hij
    have hm := nearestParticleDistance_le L X i j hij.symm
    simpa only [nearestParticleDistance,(Finset.mem_filter.mp hi).2] using hm

lemma torusDistance_triangle' (L : Length) (x y z : Torus L) :
    torusDistance L x z≤torusDistance L x y+torusDistance L y z := by
  simpa only [euclideanTorusPoint_dist] using dist_triangle
    (euclideanTorusPoint L x) (euclideanTorusPoint L y) (euclideanTorusPoint L z)

lemma nearestParticleDistance_sub_le (L : Length) (X Y : ι→Torus L) (i : ι) :
    nearestParticleDistance L Y i-nearestParticleDistance L X i≤
      torusDistance L (X i) (Y i)+torusDistance L (X (nearestLabel L X i)) (Y (nearestLabel L X i)) := by
  have hm := nearestParticleDistance_le L Y i (nearestLabel L X i) (nearestLabel_ne L X i)
  have ht := torusDistance_triangle' L (Y i) (X i) (Y (nearestLabel L X i))
  have ht' := torusDistance_triangle' L (X i) (X (nearestLabel L X i)) (Y (nearestLabel L X i))
  have hs : torusDistance L (Y i) (X i)=torusDistance L (X i) (Y i) := by
    simp only [torusDistance,dist_comm]
  rw [hs] at ht
  dsimp [nearestParticleDistance]
  dsimp [nearestParticleDistance] at hm
  linarith only [hm,ht,ht']

end HardSphere

end

end OAI
