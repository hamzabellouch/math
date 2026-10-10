import Mathlib
import OAI.Computability.MinUncut.Analysis.GaussianSmallBall

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.GaussianBudget
attribute [local instance] Classical.propDecidable
variable {X C : Type*} [Fintype X] [Fintype C]

abbrev Coordinates (X C : Type*) := X ⊕ (X ⊕ C)

def liftVector (v : X → ℝ) (σ η : ℝ) (z : C) : Coordinates X C → ℝ
  | .inl x => v x
  | .inr (.inl x) => σ*v x
  | .inr (.inr c) => if c=z then η else 0

lemma liftVector_norm_sq (v : X → ℝ) (σ η : ℝ) (z : C) :
    ‖vector (liftVector v σ η z)‖^2=(1+σ^2)*‖vector v‖^2+η^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq,vector,Fintype.sum_sum_type,liftVector,mul_pow,ite_pow,zero_pow (by norm_num : (2:ℕ)≠0)]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ring

lemma liftVector_base_norm (v : X → ℝ) (hv : ‖vector v‖=1) (z : C) :
    ‖vector (liftVector v 0 0 z)‖=1 := by
  have h := liftVector_norm_sq v 0 0 z
  rw [hv] at h
  have hn := norm_nonneg (vector (liftVector v 0 0 z))
  nlinarith

lemma liftVector_norm_pos (v : X → ℝ) (hv : ‖vector v‖=1) (σ η : ℝ) (z : C) :
    1 ≤ ‖vector (liftVector v σ η z)‖ := by
  have h := liftVector_norm_sq v σ η z
  rw [hv] at h
  have hn := norm_nonneg (vector (liftVector v σ η z))
  nlinarith [sq_nonneg σ,sq_nonneg η]

lemma liftVector_perturb_sq (v : X → ℝ) (σ η : ℝ) (z : C) :
    ‖vector (liftVector v 0 0 z)-vector (liftVector v σ η z)‖^2=
      σ^2*‖vector v‖^2+η^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq,PiLp.sub_apply,vector,Fintype.sum_sum_type,liftVector,
    zero_mul,sub_self,zero_pow (by norm_num : (2:ℕ)≠0),Finset.sum_const_zero,zero_sub,neg_sq,mul_pow]
  rw [← Finset.mul_sum]
  simp [ite_pow]

lemma liftVector_perturb_le (v : X → ℝ) (hv : ‖vector v‖=1) {σ η : ℝ}
    (hσ : 0≤σ) (hη : 0≤η) (z : C) :
    ‖vector (liftVector v 0 0 z)-vector (liftVector v σ η z)‖ ≤ σ+η := by
  have h := liftVector_perturb_sq v σ η z
  rw [hv] at h
  nlinarith [mul_nonneg hσ hη,norm_nonneg (vector (liftVector v 0 0 z)-vector (liftVector v σ η z))]

lemma delta_distance_le (η : ℝ) (z w : C) :
    (∑ c : C, ((if c=z then η else 0)-(if c=w then η else 0))^2) ≤ 4*η^2 := by
  calc
    _ ≤ ∑ c : C, (2*(if c=z then η^2 else 0)+2*(if c=w then η^2 else 0)) := by
      apply Finset.sum_le_sum
      intro c _
      split_ifs <;> nlinarith [sq_nonneg η]
    _ = _ := by simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_ite_eq',Finset.mem_univ,ite_true]; ring

lemma liftVector_distance_sq (v w : X → ℝ) (σ η : ℝ) (z z' : C) :
    ‖vector (liftVector v σ η z)-vector (liftVector w σ η z')‖^2 ≤
      (1+σ^2)*‖vector v-vector w‖^2+4*η^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq,PiLp.sub_apply,vector,Fintype.sum_sum_type,liftVector]
  simp_rw [← mul_sub,mul_pow]
  rw [← Finset.mul_sum]
  have h := delta_distance_le η z z'
  linarith

lemma liftVector_distance_le (v w : X → ℝ) {σ η : ℝ} (hσ : 0≤σ) (hη : 0≤η) (z z' : C) :
    ‖vector (liftVector v σ η z)-vector (liftVector w σ η z')‖ ≤
      (1+σ)*‖vector v-vector w‖+2*η := by
  have hs := liftVector_distance_sq v w σ η z z'
  have hD := norm_nonneg (vector v-vector w)
  have hQ := norm_nonneg (vector (liftVector v σ η z)-vector (liftVector w σ η z'))
  have hc : 0≤σ*‖vector v-vector w‖^2 := mul_nonneg hσ (sq_nonneg _)
  have hd : 0≤(1+σ)*‖vector v-vector w‖*η := mul_nonneg (mul_nonneg (by linarith) hD) hη
  apply (sq_le_sq₀ hQ (by positivity)).mp
  nlinarith only [hs,hc,hd]

lemma lift_sign_first {v : X → ℝ} (hv : ‖vector v‖=1) {σ η : ℝ}
    (hσ : 0≤σ) (hη : 0≤η) (z : C) :
    (∫ c, signFailure (score (liftVector v 0 0 z) c) (score (liftVector v σ η z) c)
      ∂Measure.pi (fun _ : Coordinates X C => gaussianReal 0 1)) ≤ 4*(σ+η) := by
  rw [integral_score_sign]
  exact (sign_inner_normalize_le (liftVector_base_norm v hv z)
    (lt_of_lt_of_le (by norm_num) (liftVector_norm_pos v hv σ η z))).trans
    (mul_le_mul_of_nonneg_left (liftVector_perturb_le v hv hσ hη z) (by norm_num))

lemma lift_sign_second {v w : X → ℝ} (hv : ‖vector v‖=1) (hw : ‖vector w‖=1)
    {σ η : ℝ} (hσ : 0≤σ) (hσ1 : σ≤1) (hη : 0≤η) (z z' : C) :
    (∫ c, signFailure (score (liftVector v σ η z) c) (score (liftVector w σ η z') c)
      ∂Measure.pi (fun _ : Coordinates X C => gaussianReal 0 1)) ≤ 4*‖vector v-vector w‖+4*η := by
  rw [integral_score_sign]
  have hn : ‖vector (liftVector w σ η z')‖=‖vector (liftVector v σ η z)‖ := by
    have h := liftVector_norm_sq v σ η z
    have h' := liftVector_norm_sq w σ η z'
    rw [hv] at h
    rw [hw] at h'
    nlinarith [norm_nonneg (vector (liftVector v σ η z)),norm_nonneg (vector (liftVector w σ η z'))]
  have hge := liftVector_norm_pos v hv σ η z
  have hp : 0<‖vector (liftVector v σ η z)‖ := by linarith
  have he := sign_inner_common_norm hp rfl hn
  have hc : 2/‖vector (liftVector v σ η z)‖ ≤ 2 := (div_le_iff₀ hp).mpr (by linarith)
  have hb := liftVector_distance_le v w hσ hη z z'
  have hd := norm_nonneg (vector v-vector w)
  exact he.trans ((mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans (by nlinarith [mul_le_mul_of_nonneg_right hσ1 hd]))
end MinUncut.GaussianBudget

end
end

end OAI
