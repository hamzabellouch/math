import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Logic.Function.Iterate

namespace OAI

universe uA

namespace PeriodicTilingThree

def forwardDiff {A : Type uA} [AddCommGroup A] (f : ℤ → A) (n : ℤ) : A :=
  f (n + 1) - f n

@[simp] theorem forwardDiff_apply {A : Type uA} [AddCommGroup A]
    (f : ℤ → A) (n : ℤ) : forwardDiff f n = f (n + 1) - f n := rfl

end PeriodicTilingThree

end OAI
