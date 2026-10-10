import Mathlib

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace FlatSimilarity
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def SymbolBounds (c : ℝ) (Af Bf : V → ℝ) : Prop :=
  0<c ∧ (∃ κ : ℝ, 0<κ ∧ ∀ x, κ≤Af x) ∧
  ContDiff ℝ ∞ Af ∧ ContDiff ℝ ∞ Bf ∧
  ∀ n : ℕ, ∃ C : ℝ, 0≤C ∧ ∀ x,
    ‖iteratedFDeriv ℝ n (fun y => Af y-c^2) x‖+‖iteratedFDeriv ℝ n Bf x‖≤
      C*(1+‖x‖)^(-(4:ℝ)-n)

def MovesClassically (Af Bf : V → ℝ) (d : C₀(V,ℂ)) (u : ℝ → C₀(V,ℂ)) : Prop :=
  u 0=d ∧ ContinuousOn u (Icc (0:ℝ) 1) ∧
  (∀ t ∈ Ioo (0:ℝ) 1, ContDiff ℝ 4 (fun x => u t x)) ∧
  (∀ t ∈ Ioo (0:ℝ) 1, ∀ n : ℕ, n≤4 → ∃ M : ℝ, ∀ x,
    ‖iteratedFDeriv ℝ n (fun y => u t y) x‖≤M) ∧
  (∀ t ∈ Ioo (0:ℝ) 1, ∃ p : V →ᵇ ℂ,
    HasDerivAt (fun r => (u r).toBCF) p t ∧ ∀ x,
    p x=-((Real.exp (-t)/16*Af (Real.exp (t/4) • x) : ℝ) : ℂ)*
      Δ (Δ (fun y => u t y)) x-(1/2+(Bf (Real.exp (t/4) • x) : ℂ))*u t x)
end FlatSimilarity

end

end OAI
