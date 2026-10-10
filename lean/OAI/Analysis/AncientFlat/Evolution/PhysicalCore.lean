import OAI.Analysis.AncientFlat.Evolution.ClassicalAncient

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian Topology
namespace FlatSimilarity
open ParametrixDilation ParametrixEvolution
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def similarityTime (t : ℝ) : ℝ := -Real.log (-t)

def physical (γ : ℝ) (v : ℝ → C₀(V,ℂ)) (t : ℝ) : C₀(V,ℂ) :=
  (Real.exp ((1/2-γ)*similarityTime t) : ℂ) • dil (-similarityTime t) (v (similarityTime t))
def physicalForce (γ : ℝ) (f : ℝ → C₀(V,ℂ)) (t : ℝ) : C₀(V,ℂ) := physical (γ-1) f t
def physicalPrincipal (Af : V → ℝ) (t : ℝ) (x : V) : ℝ :=
  Af (Real.exp (similarityTime t/4) • x)/16
def physicalPotential (Bf : V → ℝ) (t : ℝ) (x : V) : ℝ :=
  Real.exp (similarityTime t)*Bf (Real.exp (similarityTime t/4) • x)
end FlatSimilarity

end

end OAI
