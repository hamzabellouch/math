import OAI.Analysis.IrrationalRotation.Model.Rotation

namespace OAI

noncomputable section
namespace Invariant233.Rotation

def orbitProduct (θ : ℝ) (a : C(Circle, ℂ)) (n : ℕ) : C(Circle, ℂ) :=
  ∏ j ∈ Finset.range n, a.comp ⟨fun x => x + j • (θ : Circle),
    continuous_id.add continuous_const⟩

end Invariant233.Rotation

end

end OAI
