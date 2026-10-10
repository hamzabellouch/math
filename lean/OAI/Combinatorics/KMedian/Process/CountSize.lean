import Mathlib
import OAI.Combinatorics.KMedian.Process.UnbalancedActions

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential
variable {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]

omit [Fintype I] [Fintype E] in
theorem countOpening_le_one (D : Actions I E) (Δ : ℕ) (e : E) : countOpening D Δ e ≤ 1 := by
  unfold countOpening
  split_ifs <;> norm_num

 theorem heavy_action_mass_le (G : I → Finset I) (H : Finset I) {g B : ℝ}
    (hgB : g ≤ B) (hB : ∀ h, h ∉ H → mass g ((graphActions G).erase h) ≤ B)
    (e : HeavyAction (graphActions G) H) : mass g ((heavyActions (graphActions G) H).erase e) ≤ B := by
  cases e with
  | inl e => exact hB e e.property
  | inr e => simpa only [heavyActions,Sum.elim_inr,mass,card_singleton,Nat.cast_one,mul_one] using hgB

 theorem count_action_size (G : I → Finset I) (H : Finset I) {Δ : ℕ} {g B : ℝ}
    (hg : 0 ≤ g) (hgB : g ≤ B) (hB : ∀ h, h ∉ H → mass g ((graphActions G).erase h) ≤ B)
    (e : HeavyAction (graphActions G) H) :
    countOpening (heavyActions (graphActions G) H) Δ e+
      mass g (countErase (heavyActions (graphActions G) H) Δ e) ≤ B+2 := by
  have hm := (mass_mono hg (countErase_subset (heavyActions (graphActions G) H) Δ e)).trans
    (heavy_action_mass_le G H hgB hB e)
  have ha := countOpening_le_one (heavyActions (graphActions G) H) Δ e
  linarith only [ha,hm]

end MetricKMedian.FixedBatch
end
end

end OAI
