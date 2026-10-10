import OAI.Analysis.IrrationalRotation.Model.CircleTailAttenuation

namespace OAI

noncomputable section
open MeasureTheory Set
namespace Invariant233.CircleCoupling

def truncationEvent (p : CircleParameterData) (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (r : Circle → ℝ) : Set Sample :=
  {ω | (∀ i ∈ p.block j,
      (ω i).2.1 < 1 - 3 / (p.m j : ℝ) ∧ 3 / (p.m j : ℝ) < (ω i).2.2) ∧
    ω ∈ tagEvent p j ∧
    (∀ s, j < s → ∀ i ∈ p.block s,
      (ω i).2.1 < 1 - 3 * (p.K j : ℝ) / p.N s ∧
        3 * (p.K j : ℝ) / p.N s < (ω i).2.2) ∧
    1 / (j : ℝ) ≤ r (point p hr false ω) ∧
    1 / (j : ℝ) ≤ 1 - r (point p hr true ω)}

end Invariant233.CircleCoupling

end

end OAI
