import Mathlib
import OAI.Analysis.HardSphere.Geometry.InjectiveNear

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

lemma sq_le_twice_sq_of_abs_le {a b c : ℝ} (h : |a|≤b+c) : a^2≤2*b^2+2*c^2 := by
  have hn : 0≤b+c := (abs_nonneg a).trans h
  have hh := (sq_le_sq₀ (abs_nonneg a) hn).mpr h
  rw [sq_abs] at hh
  nlinarith only [hh,sq_nonneg (b-c)]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

lemma closeAmplitude_sum_sq (L : Length) {s : ℝ} (hs : 0<s) (v : Torus L) (X Y : ι→Torus L) :
    (∑ i, (closeAmplitude L s v Y i-closeAmplitude L s v X i)^2)≤
      (2+1004/s^2)*∑ i, torusDistance L (X i) (Y i)^2 := by
  have hp (i : ι) := sq_le_twice_sq_of_abs_le (closeAmplitude_sub_le L hs v X Y i)
  simp only [div_pow,sq_abs] at hp
  have hn := nearestParticleDistance_sum_sq_all L X Y
  calc
    _ ≤ ∑ i, (2*torusDistance L (X i) (Y i)^2+
        2*((nearestParticleDistance L Y i-nearestParticleDistance L X i)^2/s^2)) :=
      Finset.sum_le_sum (fun i _ ↦ hp i)
    _ = 2*(∑ i, torusDistance L (X i) (Y i)^2)+
        (2/s^2)*∑ i, (nearestParticleDistance L Y i-nearestParticleDistance L X i)^2 := by
      simp only [Finset.sum_add_distrib,Finset.mul_sum,mul_div_assoc,div_mul_eq_mul_div]
    _ ≤ 2*(∑ i, torusDistance L (X i) (Y i)^2)+
        (2/s^2)*(502*∑ i, torusDistance L (X i) (Y i)^2) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hn (by positivity)) _
    _ = _ := by ring

lemma localCloseRoot_difference_sq (L : Length) {s : ℝ} (hs : 0<s) (v : Torus L) (X Y : ι→Torus L) :
    (localCloseRoot L s v Y-localCloseRoot L s v X)^2≤
      (2+1004/s^2)*∑ i, torusDistance L (X i) (Y i)^2 := by
  let a : EuclideanSpace ℝ ι := WithLp.toLp 2 (closeAmplitude L s v Y)
  let b : EuclideanSpace ℝ ι := WithLp.toLp 2 (closeAmplitude L s v X)
  have h := abs_norm_sub_norm_le a b
  have hh := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg (a-b))).mpr h
  rw [sq_abs,EuclideanSpace.real_norm_sq_eq] at hh
  exact hh.trans (closeAmplitude_sum_sq L hs v X Y)

theorem localCloseRoot_difference (L : Length) {s : ℝ} (hs : 0<s) (hs1 : s≤1)
    (v : Torus L) (X Y : ι→Torus L) :
    |localCloseRoot L s v Y-localCloseRoot L s v X|≤
      (32/s)*Real.sqrt (∑ i, torusDistance L (X i) (Y i)^2) := by
  have hsum : 0≤∑ i, torusDistance L (X i) (Y i)^2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hsq := localCloseRoot_difference_sq L hs v X Y
  have hs2 : s^2≤1 := by nlinarith only [hs1,hs]
  have hC : 2+1004/s^2≤(32/s)^2 := by
    rw [div_pow]
    apply (le_div_iff₀ (sq_pos_of_pos hs)).mpr
    field_simp
    nlinarith only [hs2]
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by positivity) (Real.sqrt_nonneg _))).mp
  rw [sq_abs,mul_pow,Real.sq_sqrt hsum]
  exact hsq.trans (mul_le_mul_of_nonneg_right hC hsum)

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter

abbrev EuclideanConfiguration (ι : Type*) := EuclideanSpace ℝ (ι×Fin 3)

def euclideanProject {ι : Type*} (L : Length) (x : EuclideanConfiguration ι) : ι→Torus L :=
  fun i q ↦ (x (i,q) : AddCircle L.val)

lemma euclideanProject_continuous {ι : Type*} (L : Length) : Continuous (euclideanProject (ι:=ι) L) :=
  continuous_pi (fun i ↦ continuous_pi (fun q ↦
    (AddCircle.continuous_mk' L.val).comp (PiLp.continuous_apply 2 (fun _ : ι×Fin 3 ↦ ℝ) (i,q))))

lemma euclideanProject_sub {ι : Type*} (L : Length) (x y : EuclideanConfiguration ι) :
    euclideanProject L (x-y)=euclideanProject L x-euclideanProject L y := by
  ext i q
  exact QuotientAddGroup.mk_sub (AddSubgroup.zmultiples L.val) (x (i,q)) (y (i,q))

lemma euclideanProject_surjective {ι : Type*} (L : Length) : Function.Surjective (euclideanProject (ι:=ι) L) := by
  intro X
  refine ⟨WithLp.toLp 2 (fun p ↦ (AddCircle.equivIco L.val 0 (X p.1 p.2)).val),?_⟩
  ext i q
  exact AddCircle.coe_equivIco

lemma euclideanProject_total_sq {ι : Type*} [Fintype ι] (L : Length) (x y : EuclideanConfiguration ι) :
    (∑ i, torusDistance L (euclideanProject L x i) (euclideanProject L y i)^2)≤dist x y^2 := by
  have ht (i : ι) : torusDistance L (euclideanProject L x i) (euclideanProject L y i)^2=
      ∑ q : Fin 3, dist ((x (i,q):ℝ):AddCircle L.val) ((y (i,q):ℝ):AddCircle L.val)^2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
  simp_rw [ht]
  rw [dist_eq_norm,EuclideanSpace.real_norm_sq_eq,Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro q _
  have hn : dist ((x (i,q):ℝ):AddCircle L.val) ((y (i,q):ℝ):AddCircle L.val)≤|x (i,q)-y (i,q)| := by
    rw [dist_eq_norm,←AddCircle.coe_sub]
    exact QuotientAddGroup.norm_mk_le_norm
  have hh := (sq_le_sq₀ dist_nonneg (abs_nonneg _)).mpr hn
  simpa only [sq_abs,PiLp.sub_apply] using hh

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

lemma closeAmplitude_continuous (L : Length) (s : ℝ) (v : Torus L) (i : ι) :
    Continuous (fun X : ι→Torus L ↦ closeAmplitude L s v X i) := by
  unfold closeAmplitude
  apply Continuous.mul
  · apply closeRamp_lipschitz.continuous.comp
    apply continuous_const.sub
    unfold torusDistance
    fun_prop
  · exact closeRamp_lipschitz.continuous.comp
      (continuous_const.sub ((nearestParticleDistance_continuous L i).div_const s))

lemma localCloseRoot_continuous (L : Length) (s : ℝ) (v : Torus L) :
    Continuous (localCloseRoot (ι:=ι) L s v) :=
  ((PiLp.continuous_toLp 2 (fun _ : ι ↦ ℝ)).comp
    (continuous_pi (fun i ↦ closeAmplitude_continuous L s v i))).norm

theorem localCloseRoot_euclidean_lipschitz (L : Length) {s : ℝ} (hs : 0<s) (hs1 : s≤1) (v : Torus L) :
    LipschitzWith ⟨32/s,by positivity⟩
      (fun x : EuclideanConfiguration ι ↦ localCloseRoot L s v (euclideanProject L x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,abs_sub_comm]
  apply (localCloseRoot_difference L hs hs1 v (euclideanProject L x) (euclideanProject L y)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (Real.sqrt_le_sqrt (euclideanProject_total_sq L x y)).trans_eq (Real.sqrt_sq dist_nonneg)

end HardSphere

end

end OAI
