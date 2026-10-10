import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalCollisionErrorBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryBulkPrincipalCollisionError
open Construction CompensationEqualityPatterns HistoryPairSourceLaws
open HistoryCompensationBiasedKernelSum
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

def principalTest (sources : SourceFamily) (origin τ : ι → ℕ)
    (K : Ω → ∀p:Pattern τ,(Block p → CommonSample sources origin) → Block p → ℝ)
    (amp : Ω → ∀p:Pattern τ,BlockDraw p (CommonSample sources origin) → ℂ)
    (u : Ω) (p : Pattern τ) (b : BlockDraw p (CommonSample sources origin)) : ℂ :=
  amp u p b * ((∏q,K u p b.val q:ℝ):ℂ)

theorem originalBulkPrincipalSum_guard_error_le
    (sources : SourceFamily) (origin τ : ι → ℕ) (μ : FinitePrior Ω)
    (Bad : Ω → Prop)
    (K : Ω → ∀p:Pattern τ,(Block p → CommonSample sources origin) → Block p → ℝ)
    (mask : Ω → ∀p:Pattern τ,(Block p → CommonSample sources origin) → ℝ)
    (guard : Ω → ∀p:Pattern τ,BlockDraw p (CommonSample sources origin) → Prop)
    (amp : Ω → ∀p:Pattern τ,BlockDraw p (CommonSample sources origin) → ℂ)
    (W M : ℝ) (hW : 0 ≤ W) (hM : 0 ≤ M)
    (hK : ∀u p b q,0 ≤ K u p b q) (hm : ∀u p b,0 ≤ mask u p b)
    (hbudget : ∀u,μ.mass u ≠ 0 → biasedKernelSum sources origin τ (K u) (mask u) ≤ M)
    (hguard : ∀u,μ.mass u ≠ 0 → ¬Bad u → ∀p b,mask u p b.val ≠ 0 → guard u p b)
    (hamp : ∀u,μ.mass u ≠ 0 → ∀p b,mask u p b.val ≠ 0 → ‖amp u p b‖ ≤ W) :
    ‖originalBulkPrincipalSum sources origin τ μ mask
        (fun u p b => if guard u p b then principalTest sources origin τ K amp u p b else 0)-
      originalBulkPrincipalSum sources origin τ μ mask (principalTest sources origin τ K amp)‖ ≤
        W*M*μ.mean (fun u => if Bad u then 1 else 0) := by
  apply originalBulkPrincipalSum_error_le sources origin τ μ Bad K mask _ _ W M hW hM hK hm hbudget
  · intro u hu hbad p b ha
    simp only [hguard u hu hbad p b ha,ite_true]
  · intro u hu hbad p b ha
    by_cases hg : guard u p b
    · simp only [hg,ite_true,sub_self,norm_zero]
      exact mul_nonneg hW (Finset.prod_nonneg (fun q _ => hK u p b.val q))
    · simp only [hg,ite_false,zero_sub,norm_neg,principalTest,norm_mul,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (Finset.prod_nonneg (fun q _ => hK u p b.val q))]
      exact mul_le_mul_of_nonneg_right (hamp u hu p b ha)
        (Finset.prod_nonneg (fun q _ => hK u p b.val q))

end Ostmann.Arithmetic.HistoryBulkPrincipalCollisionError

end

end OAI
