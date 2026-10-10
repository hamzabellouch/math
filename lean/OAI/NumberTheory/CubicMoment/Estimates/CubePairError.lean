import OAI.NumberTheory.CubicMoment.Estimates.CubeScalar

namespace OAI

/-! The cube-lattice asymptotic at the exact scale of each Poisson entry. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cube_poisson_pair_error (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (a b : Eisenstein),
      primary a → Squarefree a → primary b → Squarefree b →
      ∀ A : ℝ, 0 < A → A ≤ 27*norm (b*a) →
      ‖(A/(9*Real.sqrt (norm (b*a))):ℝ)*
          (∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then
            gramDualTerm b a W A h else 0) -
        (A^(2/3:ℝ)*(norm (b*a))^(-(1/6:ℝ))/9:ℝ)*cubeProfileIntegral W‖ ≤
        C*A/(27*Real.sqrt (norm (b*a))) +
        K*(A^(2/3:ℝ)*(norm (b*a))^(-(1/6:ℝ))/9)*
          ∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p := by
  obtain ⟨C,K,hC,hK,hbound⟩ := cube_gram_asymptotic W hW hW'
  refine ⟨C,K,hC,hK,?_⟩
  intro a b ha hsa hb hsb A hA hAN
  have hN : 0 < norm (b*a) := norm_pos_of_ne_zero
    (mul_ne_zero (primary_ne_zero hb) (primary_ne_zero ha))
  let q := (A/(27*norm (b*a)))^(1/3:ℝ)
  have hq : 0 < q := Real.rpow_pos_of_pos (by positivity) _
  have hq1 : q ≤ 1 := Real.rpow_le_one (by positivity)
    ((div_le_one (by positivity)).mpr hAN) (by norm_num)
  have hq3 : q^3 = A/(27*norm (b*a)) := cube_poisson_root hA hN
  have hbnd := hbound a b ha hsa hb hsb A q hA.le hq hq1 hq3
  let P := A/(9*Real.sqrt (norm (b*a)))
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hscale : P*(1/(3*q)) = A^(2/3:ℝ)*(norm (b*a))^(-(1/6:ℝ))/9 :=
    cube_poisson_scale hA hN
  have hid : (P:ℂ)*(∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then
      gramDualTerm b a W A h else 0) -
      (A^(2/3:ℝ)*(norm (b*a))^(-(1/6:ℝ))/9:ℝ)*cubeProfileIntegral W =
    (P:ℂ)*((∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then
      gramDualTerm b a W A h else 0)-(1/(3*q):ℝ) • cubeProfileIntegral W) := by
    rw [mul_sub,Complex.real_smul,← mul_assoc,← Complex.ofReal_mul,hscale]
  change ‖(P:ℂ)*_ - _‖ ≤ _
  rw [hid,norm_mul,Complex.norm_real,Real.norm_of_nonneg hP]
  apply (mul_le_mul_of_nonneg_left hbnd hP).trans_eq
  calc
    P*((C+K/q*∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p)/3) =
        C*P/3 + K*(P*(1/(3*q)))*
          ∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p := by ring
    _ = _ := by rw [hscale]; dsimp [P]; ring

end CubicFirstMoment

end

end OAI
