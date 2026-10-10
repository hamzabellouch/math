import Mathlib
import OAI.Combinatorics.UniformKServer.HorizonPolicy
import OAI.Combinatorics.UniformKServer.OffsetBridge

namespace OAI

noncomputable section

/-! Exact rational offset optimization with a bound fixed before the horizon.
The optimized offset, not an unproved zero-additive theorem, funds restarts. -/
namespace UniformKServer.OffsetLP
open EffectiveLP FourierMotzkin PartitionTree
open scoped Classical
variable {n k : ℕ} [NeZero k]

 theorem uniform_offset (d : RationalMetric n) (u : Config n k) (hk : 2≤k)
    (A : ℚ) (hA : absoluteRate*(Real.log (k+1))^2≤(A : ℝ)) :
    ∃ B : ℝ,0≤B ∧ ∀H : ℕ,∃x : Fin (Fintype.card (Variable n k H)+1)→ℚ,
      optimize (Fintype.card (Variable n k H)) (constraints d u A)=some x ∧
      Valid d u A (ofAssignment (Form.recover x)) (FourierMotzkin.objective x) ∧
      ((FourierMotzkin.objective x : ℚ) : ℝ)≤B := by
  obtain ⟨B,hB⟩ := OfflineLaw.horizon_policy d u.val hk
  refine ⟨max 0 B,le_max_left _ _,?_⟩
  intro H
  obtain ⟨F,hF,hc⟩ := hB H
  have hv : Valid d u A (restrict (H:=H) F) (max 0 B) :=
    restriction_valid d u A F _ hF (le_max_left _ _) (fun w hw=>by
      have hn : 0≤offlineCost d u.val w := by
        rw [OfflineDynamic.offline_eq_optRat]
        exact EffectiveLP.opt_nonneg d u.val w
      exact (hc w hw).trans (add_le_add (mul_le_mul_of_nonneg_right hA hn) (le_max_right _ _)))
  obtain ⟨x,hx,hv',hmin⟩ := rational_attainment d u A ⟨restrict F,max 0 B,hv⟩
  exact ⟨x,hx,hv',hmin _ _ hv⟩

end UniformKServer.OffsetLP

end

end OAI
