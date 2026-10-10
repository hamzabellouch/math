import OAI.Analysis.KadisonKastler.RowOperatorFactorization
import OAI.Analysis.KadisonKastler.RowEnergyBounds
import OAI.Analysis.KadisonKastler.HilbertRows

namespace OAI

/-! The representation-side row action preserves the factorization bound. -/

namespace KadisonKastler

noncomputable section

open Generator
open scoped InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

local instance rowRepOrder : PartialOrder (K →L[ℂ] K) := CStarAlgebra.spectralOrder _
local instance rowRepStarOrder : StarOrderedRing (K →L[ℂ] K) :=
  CStarAlgebra.spectralOrderedRing _

theorem operatorRow_normalized_norm_le_one {ι : Type*} [Fintype ι]
    (s : ι → K →L[ℂ] K) (hs : ∑ i, s i * star (s i) = 1) :
    ‖operatorRow s‖ ≤ 1 := by
  classical
  have hp : operatorRow s * (operatorRow s).conjTranspose =
      (1 : CStarMatrix Unit Unit (K →L[ℂ] K)) := by
    ext1 i j
    cases i
    cases j
    simpa only [CStarMatrix.mul_apply, operatorRow_apply,
      CStarMatrix.conjTranspose_apply, CStarMatrix.one_apply, ite_eq_left] using hs
  have h := CStarRing.norm_star_mul_self (x := (1 : CStarMatrix Unit Unit (K →L[ℂ] K)))
  simp only [star_one, one_mul] at h
  have he := norm_rectangular_mul_star (operatorRow s)
  rw [hp] at he
  have h1 : ‖(1 : CStarMatrix Unit Unit (K →L[ℂ] K))‖ ≤ 1 := by
    nlinarith [norm_nonneg (1 : CStarMatrix Unit Unit (K →L[ℂ] K))]
  nlinarith [norm_nonneg (operatorRow s)]

theorem representationRowAverage_norm_le {M : VonNeumannAlgebra H}
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) {ι : Type*} [Fintype ι]
    (r : ι → Algebra M) (hr : ∑ i, r i * star (r i) = 1) (R : H →L[ℂ] K) :
    ‖representationRowAverage π r R‖ ≤ ‖R‖ := by
  have hπ : ∑ i, π (r i) * star (π (r i)) = 1 := by
    simpa only [map_sum, map_mul, map_star, map_one] using congrArg π hr
  have hrow := operatorRow_normalized_norm_le_one (fun i => π (r i)) hπ
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg R)
  intro ξ
  let v : FiniteHilbert ι K := WithLp.toLp 2 fun i => R ((star (r i) : H →L[ℂ] H) ξ)
  have hv : ‖v‖ ≤ ‖R‖ * ‖ξ‖ := by
    apply (sq_le_sq₀ (norm_nonneg v) (mul_nonneg (norm_nonneg R) (norm_nonneg ξ))).mp
    have hs : ∑ i, ‖(star (r i) : H →L[ℂ] H) ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
      have hξ : (inner ℂ ξ ξ).re = ‖ξ‖ ^ 2 := by
        simpa only [RCLike.re_eq_complex_re] using (norm_sq_eq_re_inner (𝕜 := ℂ) ξ).symm
      have h := rowAdjointVector_norm_sq r ξ
      rw [hr] at h
      simpa only [PiLp.norm_sq_eq_of_L2, rowAdjointVector, PiLp.toLp_apply,
        OneMemClass.coe_one, one_apply_eq_self, hξ] using h
    rw [PiLp.norm_sq_eq_of_L2, mul_pow]
    calc
      _ ≤ ∑ i, (‖R‖ * ‖(star (r i) : H →L[ℂ] H) ξ‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ (norm_nonneg _) (R.le_opNorm _) 2
      _ = ‖R‖ ^ 2 * ‖ξ‖ ^ 2 := by simp only [mul_pow, ← Finset.mul_sum, hs]
  have hb := norm_operatorRow_apply (fun i => π (r i)) v
  have he : (∑ i, π (r i) (v i)) = representationRowAverage π r R ξ := by
    simp [representationRowAverage, v]
  rw [he] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_right hrow (norm_nonneg v)).trans
    (by simpa only [one_mul] using hv))

end

end KadisonKastler

end OAI
