import OAI.Analysis.AncientFlat.Geometry.InteriorCore

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction ENNReal
namespace FlatWeighted
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

def sigma (p : V × ℝ) : ℝ := Real.sqrt (‖p.1‖^2+Real.sqrt (-p.2))
def chart (p q : V × ℝ) : V × ℝ := (p.1+sigma p • q.1,p.2+sigma p^4*q.2)
def localDomain (a : ℝ) (p : V × ℝ) : Set (V × ℝ) :=
  {q | ‖q.1‖<a ∧ -a^4<q.2 ∧ q.2<a^4 ∧ (chart p q).2<0}
def pullback (w : ℝ) (p : V × ℝ) (f : V × ℝ → ℂ) (q : V × ℝ) : ℂ :=
  sigma p^(-w) • f (chart p q)

def YBound (α w a M : ℝ) (f : V × ℝ → ℂ) : Prop :=
  ∀ p : V × ℝ, p.2<0 → HolderBound α (localDomain a p) (pullback (w-4) p f) M

def holderNorm (α : ℝ) (Ω : Set (V × ℝ)) (f : V × ℝ → ℂ) : ℝ≥0∞ := by
  classical
  exact (⨆ p∈Ω, ‖f p‖ₑ)+(⨆ p∈Ω, ⨆ q∈Ω, if p=q then 0 else ‖f p-f q‖ₑ/ENNReal.ofReal (pdist p q^α))
def yNorm (α w a : ℝ) (f : V × ℝ → ℂ) : ℝ≥0∞ :=
  ⨆ p : {p : V × ℝ // p.2<0}, holderNorm α (localDomain a p) (pullback (w-4) p f)

def normalizedSource (γ : ℝ) (f : V × ℝ → ℂ) (τ : ℝ) (z : V) : ℂ :=
  Real.exp ((γ-3/2)*τ) • f (Real.exp (-τ/4) • z,-Real.exp (-τ))
end FlatWeighted

end

end OAI
