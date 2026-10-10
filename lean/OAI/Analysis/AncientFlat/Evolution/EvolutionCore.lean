import OAI.Analysis.AncientFlat.Evolution.HomogeneousUniqueness

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace ParametrixEvolution
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {α β : ℝ}

def Evolves (A : C(ℝ,V →ᵇ Icc α β)) (b : C(ℝ,V →ᵇ ℂ))
    (s T : ℝ) (d : C₀(V,ℂ)) (u : ℝ → C₀(V,ℂ)) : Prop :=
  u s=d ∧ ContinuousOn u (Icc s T) ∧
  (∀ t ∈ Ioo s T, ContDiff ℝ 4 (fun x => u t x)) ∧
  (∀ t ∈ Ioo s T, ∀ n : ℕ, n≤4 → ∃ M : ℝ, ∀ x,
    ‖iteratedFDeriv ℝ n (fun y => u t y) x‖≤M) ∧
  (∀ t ∈ Ioo s T, ∃ v : V →ᵇ ℂ,
    HasDerivAt (fun r => (u r).toBCF) v t ∧ ∀ x,
      v x=-((A t x).val : ℂ)*Δ (Δ (fun y => u t y)) x-b t x*u t x)

end ParametrixEvolution

end

end OAI
