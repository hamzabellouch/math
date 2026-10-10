import Mathlib
import OAI.Combinatorics.BalancedRyser.Selection.Selection

namespace OAI

noncomputable section
namespace Balanced.FinitePushforward

def pushWeight {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (w : A → ℝ) (b : B) : ℝ :=
  ∑ a, if f a = b then w a else 0

def cylinderMass {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
    (w : (I → V) → ℝ) (J : Finset I) (a : I → V) : ℝ :=
  ∑ t, if ∀ i ∈ J, t i = a i then w t else 0

def mapChoices {I V L : Type*} (label : I → V → L) (t : I → V) : I → L :=
  fun i => label i (t i)

end Balanced.FinitePushforward

namespace Balanced.Selection

noncomputable section

def OutputLaw.labelWeight {I V L : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [Fintype L] [DecidableEq L] {G : Input I V}
    (law : OutputLaw G) (label : I → V → L) : (I → L) → ℝ :=
  FinitePushforward.pushWeight (FinitePushforward.mapChoices label) law.weight

end
end Balanced.Selection

end

end OAI
