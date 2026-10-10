import Mathlib
import OAI.Probability.LogConcave.Numerics.RowGaussian

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {d : ℕ}
lemma centerValues_mono {F : Point d → ℝ} {Q Q' : ℝ} (h : Q≤Q') (E : MeanTree X d) (x : X) :
    centerValues F Q E x → centerValues F Q' E x := by
  induction E with | node k b hb a r C ih =>
    intro he i
    exact ⟨(he i).1.trans h,ih i (he i).2⟩
end LogConcaveSampling.MeanTree

end
end

end OAI
