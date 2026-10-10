import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.UniformQuantization

def quantize (q : ℕ) [NeZero q] (x : ℝ) : Fin q :=
  ⟨⌊(q : ℝ) * x⌋₊ % q, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q))⟩

def binAverage (q : ℕ) [NeZero q] (h : ℝ → ℝ) (a : Fin q) : ℝ :=
  (q : ℝ) * ∫ x in {x | quantize q x = a}, h x ∂volume.restrict (Ico (0 : ℝ) 1)

end Invariant233.UniformQuantization

end

end OAI
