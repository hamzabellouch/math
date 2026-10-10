import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.FiniteLaw
import OAI.Probability.SKBarriers.SpinGlass.FiniteProduct

namespace OAI

section
noncomputable section
open Classical
namespace SK.Analytic.FiniteLaw
variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
theorem expect_indicator_eq_prob (P : FiniteLaw X) (E : X → Prop) [DecidablePred E] :
    P.expect (fun x => if E x then 1 else 0)=P.prob E := by
  unfold prob
  congr 1
  funext x
  split_ifs <;> rfl

theorem iid_prob_single (P : FiniteLaw X) (i : I) (E : X → Prop) :
    (P.iid I).prob (fun z => E (z i))=P.prob E := by
  exact P.iid_expect_single i (fun x => if E x then 1 else 0)

theorem iid_prob_injective (P : FiniteLaw X) (e : J → I) (he : Function.Injective e)
    (E : (J → X) → Prop) :
    (P.iid I).prob (fun z => E (z ∘ e))=(P.iid J).prob E := by
  exact P.iid_expect_injective e he (fun z => if E z then 1 else 0)

end SK.Analytic.FiniteLaw

end
end

end OAI
