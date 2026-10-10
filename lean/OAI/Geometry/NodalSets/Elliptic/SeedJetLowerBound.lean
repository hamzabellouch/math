import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import OAI.Geometry.NodalSets.Elliptic.UniformContact

namespace OAI

namespace Yau.Jets
open Set
open scoped ContDiff
noncomputable section

lemma trig_jet_lower_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p q : E) (t mu B : ℝ) (hmu : 0 < mu) (hB : 0 ≤ B) (hp : ‖p‖ ≤ B) (hq : mu ≤ ‖q‖) :
    mu/(mu+B+1) ≤ |Real.cos t|+‖Real.cos t • p-Real.sin t • q‖ := by
  have he : Real.sin t • q = Real.cos t • p-(Real.cos t • p-Real.sin t • q) := by abel
  have h := norm_sub_le (Real.cos t • p) (Real.cos t • p-Real.sin t • q)
  rw [← he,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs] at h
  have h1 : mu*|Real.sin t| ≤ B*|Real.cos t|+‖Real.cos t • p-Real.sin t • q‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hq (abs_nonneg (Real.sin t)),
      mul_le_mul_of_nonneg_left hp (abs_nonneg (Real.cos t))]
  have htrig : 1 ≤ |Real.cos t|+|Real.sin t| := by
    have hc := Real.abs_cos_le_one t
    have hs := Real.abs_sin_le_one t
    have hid := Real.sin_sq_add_cos_sq t
    nlinarith [sq_abs (Real.cos t),sq_abs (Real.sin t),abs_nonneg (Real.cos t),abs_nonneg (Real.sin t)]
  apply (div_le_iff₀ (by positivity : 0 < mu+B+1)).mpr
  nlinarith [mul_le_mul_of_nonneg_left htrig hmu.le,
    mul_nonneg hB (norm_nonneg (Real.cos t • p-Real.sin t • q)),
    mul_nonneg hmu.le (norm_nonneg (Real.cos t • p-Real.sin t • q)),abs_nonneg (Real.cos t)]

def oscillatorySeed (S T : Coord → ℝ) (N : ℝ) (x : Coord) : ℝ :=
  Real.exp (N*S x)*Real.cos (N*T x)

lemma oscillatorySeed_normalized_derivative (S T : Coord → ℝ) (N : ℝ) (x : Coord)
    (hS : DifferentiableAt ℝ S x) (hT : DifferentiableAt ℝ T x) (hN : N ≠ 0) :
    N⁻¹ • fderiv ℝ (oscillatorySeed S T N) x =
      Real.exp (N*S x) • (Real.cos (N*T x) • fderiv ℝ S x-Real.sin (N*T x) • fderiv ℝ T x) := by
  have h := ((hS.hasFDerivAt.const_mul N).exp).mul ((hT.hasFDerivAt.const_mul N).cos)
  change HasFDerivAt (oscillatorySeed S T N) _ x at h
  rw [h.fderiv]
  ext v
  simp only [smul_apply,smul_eq_mul,sub_apply,add_apply]
  field_simp
  ring

theorem uniform_oscillatory_seed_jet (S T : Coord → ℝ) (hS : ContDiff ℝ ∞ S)
    (hT : ContDiff ℝ ∞ T) {Q : Set Coord} (hQ : IsCompact Q)
    (hq : ∀ x ∈ Q, fderiv ℝ T x ≠ 0) :
    ∃ c > 0, ∀ N : ℝ, 0 < N → ∀ x ∈ Q,
      c*Real.exp (N*S x) ≤ |oscillatorySeed S T N x|+N⁻¹*‖fderiv ℝ (oscillatorySeed S T N) x‖ := by
  obtain ⟨mu,hmu,_,_,hql⟩ := compact_positive_bounds hQ (fun x ↦ ‖fderiv ℝ T x‖)
    (hT.continuous_fderiv (by simp)).norm.continuousOn (fun x hx ↦ norm_pos_iff.mpr (hq x hx))
  obtain ⟨B,hB,hpb⟩ := (hQ.image (hS.continuous_fderiv (by simp))).isBounded.exists_pos_norm_le
  refine ⟨mu/(mu+B+1),by positivity,?_⟩
  intro N hN x hx
  have hb := trig_jet_lower_bound (fderiv ℝ S x) (fderiv ℝ T x) (N*T x) mu B hmu hB.le
    (hpb _ ⟨x,hx,rfl⟩) (hql x hx).1
  have hd := congrArg norm (oscillatorySeed_normalized_derivative S T N x
    (hS.differentiable (by simp)).differentiableAt (hT.differentiable (by simp)).differentiableAt hN.ne')
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hN),abs_of_pos (Real.exp_pos _)] at hd
  rw [hd]
  simpa only [oscillatorySeed,abs_mul,abs_of_pos (Real.exp_pos _),mul_add,mul_comm] using
    mul_le_mul_of_nonneg_left hb (Real.exp_pos (N*S x)).le

end
end Yau.Jets

end OAI
