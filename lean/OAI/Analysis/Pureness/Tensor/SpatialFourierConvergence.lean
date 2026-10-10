import OAI.Analysis.Pureness.Tensor.SpatialFiniteFourier
import OAI.Analysis.Pureness.Tensor.SpatialGroupPolynomialDensity
import OAI.Analysis.Pureness.Operators.DenseOperatorConvergence

namespace OAI
noncomputable section
namespace CuntzPureness
local instance spatialFourierConvergenceDecidableEq {X : Type*} : DecidableEq X := Classical.decEq X
open scoped TensorProduct
open Filter Topology
variable {A H G : Type*} [Group G] [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hα : Function.Injective α)

include hα in

theorem spatialFiniteFourier_tendsto_of_uniform_bound
    (s : ℕ → Finset G) (c : ℕ → G → ℂ) (C : ℝ)
    (hbound : ∀ n x, ‖spatialFiniteFourier (G := G) α (s n) (c n) x‖ ≤ C * ‖x‖)
    (hcoeff : ∀ g, Tendsto (fun n => if g ∈ s n then c n g else 0) atTop (nhds 1))
    (x : representedSpatialTensor α (reducedGroupAlgebra G).subtype) :
    Tendsto (fun n => spatialFiniteFourier (G := G) α (s n) (c n) x) atTop (nhds x) := by
  apply boundedOperators_tendsto_of_dense_span
    (fun p : A × G => spatialCompletionMap α (reducedGroupAlgebra G).subtype
      (p.1 ⊗ₜ[ℂ] (reducedGroupUnitary G p.2 : reducedGroupAlgebra G)))
    (spatialGroupPolynomial_dense α) (fun n => spatialFiniteFourier (G := G) α (s n) (c n)) C hbound
  intro p
  simp only [spatialFiniteFourier_generator α hα]
  simpa only [one_smul] using (hcoeff p.2).smul_const
    (spatialCompletionMap α (reducedGroupAlgebra G).subtype
      (p.1 ⊗ₜ[ℂ] (reducedGroupUnitary G p.2 : reducedGroupAlgebra G)))

include hα in

theorem spatialFiniteFourier_tendsto_of_exhaustion
    (s : ℕ → Finset G) (c : ℕ → G → ℂ) (C : ℝ)
    (hbound : ∀ n x, ‖spatialFiniteFourier (G := G) α (s n) (c n) x‖ ≤ C * ‖x‖)
    (hs : ∀ g, ∀ᶠ n in atTop, g ∈ s n)
    (hc : ∀ g, Tendsto (fun n => c n g) atTop (nhds 1))
    (x : representedSpatialTensor α (reducedGroupAlgebra G).subtype) :
    Tendsto (fun n => spatialFiniteFourier (G := G) α (s n) (c n) x) atTop (nhds x) := by
  apply spatialFiniteFourier_tendsto_of_uniform_bound α hα s c C hbound
  intro g
  apply (hc g).congr'
  filter_upwards [hs g] with n hn
  exact (ite_eq_left hn).symm
end CuntzPureness

end

end OAI
