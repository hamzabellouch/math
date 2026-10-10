import OAI.Analysis.AncientFlat.Weighted.WeightedCharts

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ENNReal
namespace FlatWeighted
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

def finiteLocalDomain (T a : ℝ) (p : V × ℝ) : Set (V × ℝ) :=
  {q | ‖q.1‖<a ∧ -a^4<q.2 ∧ q.2<a^4 ∧ -T≤(chart p q).2 ∧ (chart p q).2<0}
def finiteYNorm (α w a T : ℝ) (f : V × ℝ → ℂ) : ℝ≥0∞ :=
  ⨆ p : {p : V × ℝ // -T≤p.2 ∧ p.2<0},
    holderNorm α (finiteLocalDomain T a p.val) (pullback (w-4) p.val f)

def innerExtension (ψ : ℝ → ℝ) (T : ℝ) (f : V × ℝ → ℂ) (p : V × ℝ) : ℂ :=
  if -T≤p.2 then f p else
    ψ ((-p.2-T)/(‖p.1‖^2+Real.sqrt T)^2) • f (p.1,-T)
def ExtensionCutoff (ψ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ ψ ∧ (∀ s : ℝ, 0 ≤ s → 0≤ψ s ∧ ψ s≤1) ∧
  (∃ ε : ℝ, 0<ε ∧ ∀ s ∈ Icc 0 ε, ψ s=1) ∧ (∀ s : ℝ, 1 ≤ s → ψ s=0)
end FlatWeighted

end

end OAI
