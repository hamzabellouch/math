import Mathlib
import OAI.Analysis.HardSphere.Comparison.FiniteFiberSum

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

lemma exists_injective_near {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [MetricSpace E] [PerfectSpace E] (X : ι→E) {ε : ℝ} (hε : 0<ε) :
    ∃ Y : ι→E, Function.Injective Y ∧ ∀ i, dist (Y i) (X i)<ε := by
  classical
  have aux (I : Finset ι) : ∃ Y : ι→E, Set.InjOn Y I ∧ ∀ i∈I, dist (Y i) (X i)<ε := by
    induction I using Finset.induction_on with
    | empty => exact ⟨X,by simp [Set.InjOn],by simp⟩
    | @insert a I ha ih =>
      obtain ⟨Y,hinj,hclose⟩ := ih
      have hd := dense_univ.sdiff_finset (I.image Y)
      obtain ⟨y,hy,hball⟩ := hd.exists_mem_open Metric.isOpen_ball (Metric.nonempty_ball.mpr hε)
      refine ⟨Function.update Y a y,?_,?_⟩
      · intro i hi j hj he
        rcases Finset.mem_insert.mp hi with hi | hi
        · subst i
          rcases Finset.mem_insert.mp hj with hj | hj
          · exact hj.symm
          · have hja : j≠a := fun h ↦ ha (h ▸ hj)
            rw [Function.update_self,Function.update_of_ne hja] at he
            exact (hy.2 (by rw [he]; exact Finset.mem_image.mpr ⟨j,hj,rfl⟩)).elim
        · rcases Finset.mem_insert.mp hj with hj | hj
          · subst j
            have hia : i≠a := fun h ↦ ha (h ▸ hi)
            rw [Function.update_self,Function.update_of_ne hia] at he
            exact (hy.2 (Finset.mem_image.mpr ⟨i,hi,he⟩)).elim
          · have hia : i≠a := fun h ↦ ha (h ▸ hi)
            have hja : j≠a := fun h ↦ ha (h ▸ hj)
            rw [Function.update_of_ne hia,Function.update_of_ne hja] at he
            exact hinj hi hj he
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simpa using hball
        · rw [Function.update_of_ne (show i≠a from fun h ↦ ha (h ▸ hi))]
          exact hclose i hi
  obtain ⟨Y,hi,hc⟩ := aux Finset.univ
  exact ⟨Y,fun i j h ↦ hi (Finset.mem_univ _) (Finset.mem_univ _) h,fun i ↦ hc i (Finset.mem_univ _)⟩

lemma dense_injective_configurations {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [MetricSpace E] [PerfectSpace E] : Dense {X : ι→E | Function.Injective X} := by
  apply Metric.dense_iff.mpr
  intro X ε hε
  obtain ⟨Y,hY,hclose⟩ := exists_injective_near X hε
  refine ⟨Y,?_,hY⟩
  exact (dist_pi_lt_iff hε).mpr hclose

lemma torus_nontrivial (L : Length) : Nontrivial (Torus L) := by
  let hc : Nontrivial (AddCircle L.val) := by
    refine ⟨⟨((L.val/2:ℝ):AddCircle L.val),0,?_⟩⟩
    intro he
    have hh := AddCircle.norm_half_period_eq L.val
    rw [he,norm_zero,abs_of_pos L.property] at hh
    linarith only [L.property,hh]
  let := hc
  infer_instance

lemma torusDistance_continuous_pair (L : Length) :
    Continuous (fun p : Torus L×Torus L ↦ torusDistance L p.1 p.2) := by
  unfold torusDistance
  fun_prop

attribute [local irreducible] torusDistance nearestParticleDistance

lemma nearestDifference_continuous {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (L : Length) : Continuous (fun p : (ι→Torus L)×(ι→Torus L) ↦
      ∑ i, (nearestParticleDistance L p.2 i-nearestParticleDistance L p.1 i)^2) := by
  apply continuous_finsetSum
  intro i _
  exact (((nearestParticleDistance_continuous L i).comp continuous_snd).sub
    ((nearestParticleDistance_continuous L i).comp continuous_fst)).pow 2

lemma torusMotion_continuous {ι : Type*} [Fintype ι] (L : Length) :
    Continuous (fun p : (ι→Torus L)×(ι→Torus L) ↦ 502*∑ i, torusDistance L (p.1 i) (p.2 i)^2) := by
  apply continuous_const.mul
  apply continuous_finsetSum
  intro i _
  apply Continuous.pow
  exact (torusDistance_continuous_pair L).comp
    (f := fun p : (ι→Torus L)×(ι→Torus L) ↦ (p.1 i,p.2 i))
    (((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd))

theorem nearestParticleDistance_sum_sq_all {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (L : Length) (X Y : ι→Torus L) :
    (∑ i, (nearestParticleDistance L Y i-nearestParticleDistance L X i)^2)≤
      502*∑ i, torusDistance L (X i) (Y i)^2 := by
  let := torus_nontrivial L
  let S : Set (ι→Torus L) := {X | Function.Injective X}
  have hd : Dense (S×ˢS) := dense_injective_configurations.prod dense_injective_configurations
  have hc : IsClosed {p : (ι→Torus L)×(ι→Torus L) |
      (∑ i, (nearestParticleDistance L p.2 i-nearestParticleDistance L p.1 i)^2)≤
        502*∑ i, torusDistance L (p.1 i) (p.2 i)^2} :=
    isClosed_le (nearestDifference_continuous L) (torusMotion_continuous L)
  exact closure_minimal (fun p hp ↦ nearestParticleDistance_sum_sq L p.1 p.2 hp.1 hp.2) hc (hd (X,Y))

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter

def closeRamp (t : ℝ) : ℝ := max 0 (min 1 t)

lemma closeRamp_nonneg (t : ℝ) : 0≤closeRamp t := le_max_left _ _
lemma closeRamp_le_one (t : ℝ) : closeRamp t≤1 := max_le zero_le_one (min_le_left _ _)
lemma closeRamp_one {t : ℝ} (ht : 1≤t) : closeRamp t=1 := by simp [closeRamp,min_eq_left ht]
lemma closeRamp_zero {t : ℝ} (ht : t≤0) : closeRamp t=0 := by
  exact max_eq_left ((min_le_right 1 t).trans ht)
lemma closeRamp_lipschitz : LipschitzWith 1 closeRamp :=
  (LipschitzWith.id.const_min 1).const_max 0

lemma closeRamp_sub_le (x y : ℝ) : |closeRamp x-closeRamp y|≤|x-y| := by
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using closeRamp_lipschitz.dist_le_mul x y

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

def closeAmplitude (L : Length) (s : ℝ) (v : Torus L) (X : ι→Torus L) (i : ι) : ℝ :=
  closeRamp (6-torusDistance L (X i) v)*closeRamp (2-nearestParticleDistance L X i/s)

def localCloseRoot (L : Length) (s : ℝ) (v : Torus L) (X : ι→Torus L) : ℝ :=
  ‖(WithLp.toLp 2 (closeAmplitude L s v X) : EuclideanSpace ℝ ι)‖

def localCloseSmoothCount (L : Length) (s : ℝ) (v : Torus L) (X : ι→Torus L) : ℝ :=
  ∑ i, closeAmplitude L s v X i^2

lemma localCloseRoot_sq (L : Length) (s : ℝ) (v : Torus L) (X : ι→Torus L) :
    localCloseRoot L s v X^2=localCloseSmoothCount L s v X :=
  EuclideanSpace.real_norm_sq_eq _

lemma closeAmplitude_nonneg (L : Length) (s : ℝ) (v : Torus L) (X : ι→Torus L) (i : ι) :
    0≤closeAmplitude L s v X i := mul_nonneg (closeRamp_nonneg _) (closeRamp_nonneg _)
lemma closeAmplitude_le_one (L : Length) (s : ℝ) (v : Torus L) (X : ι→Torus L) (i : ι) :
    closeAmplitude L s v X i≤1 :=
  (mul_le_of_le_one_left (closeRamp_nonneg _) (closeRamp_le_one _)).trans
    (closeRamp_le_one _)

lemma closeAmplitude_one (L : Length) {s : ℝ} (hs : 0<s) (v : Torus L) (X : ι→Torus L) (i : ι)
    (hv : torusDistance L (X i) v≤5) (hc : nearestParticleDistance L X i ≤ s) :
    closeAmplitude L s v X i=1 := by
  unfold closeAmplitude
  have hd : nearestParticleDistance L X i/s≤1 := (div_le_one hs).mpr hc
  rw [closeRamp_one (by linarith only [hv]),closeRamp_one (by linarith only [hd]),mul_one]

lemma closeAmplitude_zero_of_far (L : Length) (s : ℝ) (v : Torus L) (X : ι→Torus L) (i : ι)
    (hv : 6≤torusDistance L (X i) v) : closeAmplitude L s v X i=0 := by
  unfold closeAmplitude
  rw [closeRamp_zero (by linarith only [hv]),zero_mul]

lemma closeAmplitude_zero_of_isolated (L : Length) {s : ℝ} (hs : 0<s) (v : Torus L) (X : ι→Torus L) (i : ι)
    (hc : 2*s≤nearestParticleDistance L X i) : closeAmplitude L s v X i=0 := by
  unfold closeAmplitude
  have hd : 2≤nearestParticleDistance L X i/s := (le_div_iff₀ hs).mpr hc
  rw [closeRamp_zero (t := 2-nearestParticleDistance L X i/s) (by linarith only [hd]),mul_zero]

lemma torusDistance_sub_le (L : Length) (x y v : Torus L) :
    |torusDistance L x v-torusDistance L y v|≤torusDistance L x y := by
  simpa only [euclideanTorusPoint_dist] using abs_dist_sub_le
    (euclideanTorusPoint L x) (euclideanTorusPoint L y) (euclideanTorusPoint L v)

lemma unit_product_sub_le {a b c d : ℝ} (ha : 0≤a) (_hb : 0≤b) (_hc : 0≤c) (hd : 0≤d)
    (hA : a≤1) (_hB : b≤1) (_hC : c≤1) (hD : d≤1) :
    |a*b-c*d|≤|a-c|+|b-d| := by
  calc
    _ = |a*(b-d)+(a-c)*d| := by congr 1; ring
    _ ≤ |a*(b-d)|+|(a-c)*d| := abs_add_le _ _
    _ = a*|b-d|+|a-c| *d := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hd]
    _ ≤ 1*|b-d|+|a-c| *1 := add_le_add
      (mul_le_mul_of_nonneg_right hA (abs_nonneg _)) (mul_le_mul_of_nonneg_left hD (abs_nonneg _))
    _ = _ := by ring

lemma closeAmplitude_sub_le (L : Length) {s : ℝ} (hs : 0<s) (v : Torus L) (X Y : ι→Torus L) (i : ι) :
    |closeAmplitude L s v Y i-closeAmplitude L s v X i|≤
      torusDistance L (X i) (Y i)+|nearestParticleDistance L Y i-nearestParticleDistance L X i|/s := by
  unfold closeAmplitude
  apply (unit_product_sub_le (closeRamp_nonneg _) (closeRamp_nonneg _) (closeRamp_nonneg _) (closeRamp_nonneg _)
    (closeRamp_le_one _) (closeRamp_le_one _) (closeRamp_le_one _) (closeRamp_le_one _)).trans
  apply add_le_add
  · apply (closeRamp_sub_le _ _).trans
    have he : (6-torusDistance L (Y i) v)-(6-torusDistance L (X i) v)=
        torusDistance L (X i) v-torusDistance L (Y i) v := by ring
    rw [he]
    exact torusDistance_sub_le L (X i) (Y i) v
  · apply (closeRamp_sub_le _ _).trans_eq
    rw [show (2-nearestParticleDistance L Y i/s)-(2-nearestParticleDistance L X i/s)=
      -(nearestParticleDistance L Y i-nearestParticleDistance L X i)/s by ring,
      abs_div,abs_neg,abs_of_pos hs]

end HardSphere

end

end OAI
