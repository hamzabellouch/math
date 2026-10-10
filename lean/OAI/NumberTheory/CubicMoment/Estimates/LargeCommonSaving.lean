import OAI.NumberTheory.CubicMoment.Estimates.LargeCommonNonzero
import OAI.NumberTheory.CubicMoment.Estimates.CommonNonzeroPower

namespace OAI

/-! Every large common factor is controlled after its exact zero mode
has been removed. The divisor-energy loss leaves a fixed power saving. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem large_common_nonzero_power {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (v : Eisenstein → ℂ)
      (A N : ℝ), 0 < A → 1 ≤ N → N^(1-δ) ≤ A →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ 2*N) →
      ‖∑ k ∈ (commonRowFactors S).filter (fun k => N^δ ≤ norm k),
        (commonGramBlock S v V A k-commonGramZeroMode S v V A k)‖ ≤
      K*A^(2/3:ℝ)*N^(2/3-δ/8)*∑ a ∈ S, ‖v a‖^2 := by
  obtain ⟨C,E,hC,hE,hbound⟩ := large_common_nonzero_bound
    (ε := δ/100) (ζ := δ/8) (by positivity) (by linarith) (by positivity) V hV hV'
  refine ⟨3*C*(2:ℝ)^(δ/100)*E*(2:ℝ)^(δ/8),by positivity,?_⟩
  intro S v A N hA hN hAN hS
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hb := hbound S v A N (N^δ) hA hN (Real.one_le_rpow hN hδ.le) hS
  have hc := commonNonzeroCost_power_saving hC.le (by norm_num : (0:ℝ) ≤ 2)
    (by norm_num : (0:ℝ) ≤ 1) hN hN hA hδ hδ₁ (le_refl δ) hAN
  apply hb.trans
  calc
    _ ≤ (3*C*(2:ℝ)^(δ/100)*A^(2/3:ℝ)*N^(2/3:ℝ)*N^(-δ/4))*
        (E*(2*N)^(δ/8)*∑ a ∈ S, ‖v a‖^2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hNp.le]
      have he : N^(2/3:ℝ)*N^(-δ/4)*N^(δ/8) = N^(2/3-δ/8) := by
        rw [← Real.rpow_add hNp,← Real.rpow_add hNp]
        congr 1
        ring
      calc
        _ = (3*C*(2:ℝ)^(δ/100)*E*(2:ℝ)^(δ/8))*A^(2/3:ℝ)*
          (N^(2/3:ℝ)*N^(-δ/4)*N^(δ/8))*∑ a ∈ S, ‖v a‖^2 := by ring
        _ = _ := by rw [he]

end CubicFirstMoment

end

end OAI
