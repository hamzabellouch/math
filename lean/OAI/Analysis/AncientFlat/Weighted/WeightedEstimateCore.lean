import OAI.Analysis.AncientFlat.Weighted.WeightedLocalCore
import OAI.Analysis.AncientFlat.Profile.AnnularProfileCore

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace FlatWeighted
open ParabolicInterior ParabolicAnnular
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
def weightedValue (w : ℝ) (p : V × ℝ) (u : ℝ → V → ℂ) : ℝ → V → ℂ :=
  fun t x => sigma p^(-w) • u (chart p (x,t)).2 (chart p (x,t)).1
def weightedTime (w : ℝ) (p : V × ℝ) (ut : ℝ → V → ℂ) : ℝ → V → ℂ :=
  fun t x => (sigma p^(-w)*sigma p^4) • ut (chart p (x,t)).2 (chart p (x,t)).1

def LocallyFiniteJets (α : ℝ) (u ut : ℝ → V → ℂ) : Prop :=
  ∀ R : ℝ, 0<R → ∀ b : ℝ, b<0 → ∃ N : ℝ, 0≤N ∧
    JetBound α {p : V × ℝ | ‖p.1‖≤R ∧ -R≤p.2 ∧ p.2≤b} u ut N
def XBound (α w a M : ℝ) (u ut : ℝ → V → ℂ) : Prop :=
  ∀ p : V × ℝ, p.2<0 → JetBound α (localDomain a p)
    (weightedValue w p u) (weightedTime w p ut) M
end FlatWeighted

end

end OAI
