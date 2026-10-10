import OAI.NumberTheory.TotientAsymptotic.CoordinateViolationCount
import OAI.NumberTheory.TotientAsymptotic.CoordinateErrorBudget

namespace OAI

/-! Exponential form of the weighted-coordinate count. The hypotheses record
only numerical budgets, so the dimension and the excess may vary with X. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma coordinate_grid_prefactor (k K : ℕ) :
    (k:ℝ)*(K+1:ℕ)^k ≤
      Real.exp (Real.log ((k:ℝ)+1)+(k:ℝ)*Real.log ((K:ℝ)+1)) := by
  rw [Real.exp_add,Real.exp_log (by positivity : 0 < (k:ℝ)+1),
    Real.exp_nat_mul,Real.exp_log (by positivity : 0 < (K:ℝ)+1)]
  push_cast
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

theorem coordinate_exponential_count : ∃ C D A F : ℝ,
    0 < C ∧ 0 < D ∧ 0 < A ∧ 0 < F ∧
    ∀ X k K L J : ℕ,256 ≤ X → Real.exp (Real.exp 1) ≤ X → 1 ≤ B X →
    3 ≤ L → L ≤ K → (K:ℝ) ≤ B X →
    B X-Real.log (20*B X)-2 ≤ K →
    Real.exp K ≤ Real.log X/(20*B X) → 1 ≤ J → (X:ℝ) ≤ (2:ℝ)^J →
    ∀ ω : ℝ,0 ≤ ω → ω ≤ 1 →
    (L:ℝ)*((k:ℝ)+2)^6 ≤ ω^2*B X/1000000 →
    (Real.log (20*B X)+9+F+Real.log (B X+1))*((k:ℝ)+2)^2 ≤ ω*B X/100 →
    ((L:ℝ)+1)*(k:ℝ)^2 < (1+ω)*B X →
    ∀ Q : Finset ℕ,(∀ v ∈ Q,IsTotient v ∧ v ≤ X ∧
      ∃ n : ℕ,0 < n ∧ n.totient=v ∧
        (1+ω)*B X ≤ ∑ j : Fin k,a (j.val+1)*fordPrimeCoordinate n (j.val+1)) →
    (Q.card:ℝ) ≤ C*X*(Real.log X)^(-5/4:ℝ)+(2*X+D*X*B X)/(loglogCutoff L+1:ℕ)+
      A*dyadicTotientEnvelope J*X/Real.log X*(B (2*X))^5*(1+Real.log J)*
        (Real.log (loglogCutoff L))^(-1/6:ℝ)+
      F*X*Real.exp (-(1+ω/2)*B X) := by
  obtain ⟨C,D,A,F,hC,hD,hA,hF,hcount⟩ := coordinate_violation_count
  refine ⟨C,D,A,F,hC,hD,hA,hF,?_⟩
  intro X k K L J hX hx hB hL hLK hK hKlo hgrid hJ hxJ ω hω hω1 hsmall hbudget hT Q hQ
  have hcut := loglogCutoff_bounds (show (2:ℝ) ≤ L by exact_mod_cast (show 2 ≤ L by omega))
  have hu : 0 ≤ B (loglogCutoff L) := by
    have hLR : (3:ℝ) ≤ L := by exact_mod_cast hL
    linarith [hcut.2.1]
  have he := coordinate_exponent_budget hB hω hω1 hF.le (Nat.cast_nonneg L)
    hu hcut.2.2.1 hK hKlo hsmall hbudget
  have hp := coordinate_grid_prefactor k K
  have hlast : F*X*k*(K+1:ℕ)^k*Real.exp
      (-(1+ω)*B X+(B X+L+6-K)*(k:ℝ)^2+((k:ℝ)+2)^2*B (loglogCutoff L)+
        F*((k:ℝ)+2)^2+((k:ℝ)+2)^3*Real.sqrt (B (loglogCutoff L)*K)) ≤
      F*X*Real.exp (-(1+ω/2)*B X) := by
    calc
      _ = (F*X)*((k:ℝ)*(K+1:ℕ)^k)*Real.exp _ := by ring
      _ ≤ (F*X)*Real.exp (Real.log ((k:ℝ)+1)+(k:ℝ)*Real.log ((K:ℝ)+1))*Real.exp _ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp (by positivity)) (Real.exp_pos _).le
      _ = F*X*Real.exp
          (Real.log ((k:ℝ)+1)+(k:ℝ)*Real.log ((K:ℝ)+1)-(1+ω)*B X+
            (B X+L+6-K)*(k:ℝ)^2+((k:ℝ)+2)^2*B (loglogCutoff L)+
            F*((k:ℝ)+2)^2+((k:ℝ)+2)^3*Real.sqrt (B (loglogCutoff L)*K)) := by
        rw [mul_assoc,← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)
  exact (hcount X k K L J hX hx hB hL hLK (by linarith) hgrid hJ hxJ
    ((1+ω)*B X) hT Q hQ).trans (add_le_add le_rfl (by simpa only [neg_mul] using hlast))

end TotientAsymptotic

end

end OAI
