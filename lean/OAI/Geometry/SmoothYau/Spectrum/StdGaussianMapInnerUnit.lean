import Mathlib

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace YauCounterexamples

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_map_inner_unit (a : E) (ha : ‖a‖ = 1) :
    (stdGaussian E).map (fun x => ⟪a, x⟫) = gaussianReal 0 1 := by
  change (stdGaussian E).map (innerSL ℝ a) = _
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian]
  simp [ha]

theorem stdGaussian_map_orthonormal_pair (a c : E) (ha : ‖a‖ = 1) (hc : ‖c‖ = 1)
    (hac : ⟪a, c⟫ = 0) :
    (stdGaussian E).map (fun x => (⟪a, x⟫, ⟪c, x⟫)) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  have hlaw : HasGaussianLaw (fun x : E => (⟪a, x⟫, ⟪c, x⟫)) (stdGaussian E) := by
    exact (IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map_fun
      ((innerSL ℝ a).prod (innerSL ℝ c))
  have hcov : cov[fun x : E => ⟪a, x⟫, fun x : E => ⟪c, x⟫; stdGaussian E] = 0 := by
    rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covarianceBilin_stdGaussian]
    exact hac
  rw [(hlaw.indepFun_of_covariance_eq_zero hcov).map_prod_eq_prod_map_map
    (by fun_prop) (by fun_prop), stdGaussian_map_inner_unit a ha,
    stdGaussian_map_inner_unit c hc]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

theorem correlated_pair_orthogonal (a b : E) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hρ : |⟪a, b⟫| < 1) :
    let ρ := ⟪a, b⟫
    let s := Real.sqrt (1 - ρ ^ 2)
    let c := s⁻¹ • (b - ρ • a)
    ‖c‖ = 1 ∧ ⟪a, c⟫ = 0 ∧ b = ρ • a + s • c := by
  dsimp only
  let ρ := ⟪a, b⟫
  let s := Real.sqrt (1 - ρ ^ 2)
  have hr : 0 < 1 - ρ ^ 2 := by
    dsimp only [ρ]
    nlinarith [abs_lt.mp hρ]
  have hs : 0 < s := Real.sqrt_pos.mpr hr
  have hs2 : s ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt hr.le
  have haa : ⟪a, a⟫ = 1 := by simp [ha]
  have hbb : ⟪b, b⟫ = 1 := by simp [hb]
  have hnorm : ‖b - ρ • a‖ ^ 2 = s ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, haa, hbb]
    rw [real_inner_comm a b]
    change 1 - ρ * ρ - (ρ * ρ - ρ * (ρ * 1)) = s ^ 2
    nlinarith
  have hnorm' : ‖b - ρ • a‖ = s := by
    nlinarith [norm_nonneg (b - ρ • a)]
  refine ⟨?_, ?_, ?_⟩
  · change ‖s⁻¹ • (b - ρ • a)‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, hnorm', inv_mul_cancel₀ hs.ne']
  · change ⟪a, s⁻¹ • (b - ρ • a)⟫ = 0
    simp only [real_inner_smul_right, inner_sub_right, haa]
    change s⁻¹ * (ρ - ρ * 1) = 0
    ring
  · change b = ρ • a + s • (s⁻¹ • (b - ρ • a))
    rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    abel

end YauCounterexamples

end

end OAI
