import Mathlib.Analysis.InnerProductSpace.Basic

namespace OAI

universe uE

namespace ThompsonNonamenability

abbrev UnitBall (E : Type uE) [SeminormedAddCommGroup E] := {x : E // ‖x‖ ≤ 1}

def unitBallZero (E : Type uE) [SeminormedAddCommGroup E] : UnitBall E :=
  ⟨0, by simp⟩

@[simp] theorem coe_unitBallZero (E : Type uE) [SeminormedAddCommGroup E] :
    (unitBallZero E : E) = 0 := rfl

theorem unitBall_norm_le {E : Type uE} [SeminormedAddCommGroup E] (x : UnitBall E) :
    ‖(x : E)‖ ≤ 1 := x.property

end ThompsonNonamenability

end OAI
