import OAI.Analysis.AncientFlat.Kernel.SymbolCore

namespace OAI
noncomputable section
open scoped ZeroAtInfty
namespace FlatSimilarity
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def TimeOneMap (Af Bf : V → ℝ) (P : C₀(V,ℂ) →L[ℂ] C₀(V,ℂ)) : Prop :=
  ∀ d : C₀(V,ℂ), ∃ u : ℝ → C₀(V,ℂ), MovesClassically Af Bf d u ∧
    ∀ x, P d x=u 1 (Real.exp (-(1:ℝ)/4) • x)
end FlatSimilarity

end

end OAI
