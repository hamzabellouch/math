import OAI.Analysis.AncientFlat.Evolution.PreliminaryAncient
import OAI.Analysis.AncientFlat.Evolution.RenormalizedSource

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian Topology
namespace FlatSimilarity
open ParametrixDilation ParametrixEvolution
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def AncientClassical (Af Bf : V → ℝ) (γ : ℝ) (f v : ℝ →ᵇ C₀(V,ℂ)) : Prop :=
  (∀ t : ℝ, ContDiff ℝ 4 (fun x => v t x)) ∧
  (∀ t : ℝ, ∀ n : ℕ, n≤4 → ∃ M : ℝ, ∀ x,
    ‖iteratedFDeriv ℝ n (fun y => v t y) x‖≤M) ∧
  (∀ t : ℝ, ∀ x : V, HasDerivAt (fun r => v r x)
    (f t x-(Af x/16 : ℝ) • Δ (Δ (fun y => v t y)) x-
      (1/2-γ+Bf x : ℝ) • v t x-(1/4 : ℝ) • (fderiv ℝ (fun y => v t y) x x)) t)
end FlatSimilarity

end

end OAI
