import OAI.Analysis.Pureness.GroupAlgebra.FreeGroupRadialKernel
import OAI.Analysis.Pureness.Tensor.SpatialSymbolMultiplier

namespace OAI
noncomputable section
namespace CuntzPureness
local instance spatialFreeGroupRadialDecidableEq {X : Type*} : DecidableEq X := Classical.decEq X
open scoped TensorProduct
open Filter Topology
variable {A H X : Type*} [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hα : Function.Injective α)

def freeGroupRadialSymbol (r : ℝ) (g : FreeGroup X) : ℂ := ((r ^ g.toWord.length : ℝ) : ℂ)

def spatialFreeGroupRadial (r : ℝ) :
    representedSpatialTensor α (reducedGroupAlgebra (FreeGroup X)).subtype →L[ℂ]
      representedSpatialTensor α (reducedGroupAlgebra (FreeGroup X)).subtype :=
  spatialSymbolMultiplier α (freeGroupRadialSymbol (X := X) r)

include hα in
lemma spatialFreeGroupRadial_polynomial_bound (r : ℝ) (hr : |r| ≤ 1)
    (a : FreeGroup X →₀ A) :
    ‖spatialGroupPolynomialMap (G := FreeGroup X) α (groupPolynomialWeight
      (freeGroupRadialSymbol (X := X) r) a)‖ ≤
        1 * ‖spatialGroupPolynomialMap (G := FreeGroup X) α a‖ := by
  exact (spatialGroupPolynomialWeight_norm_le α hα
    (freeGroupRadialSymbol (X := X) r)
    (freeGroupRadialVector r) (freeGroupRadialVector r)
    (fun g => (freeGroupRadialVector_norm r hr g).le)
    (fun g => (freeGroupRadialVector_norm r hr g).le)
    (fun g h => (freeGroupRadialVector_inner r hr g h).symm) a).trans_eq (one_mul _).symm

include hα in
theorem spatialFreeGroupRadial_norm_le (r : ℝ) (hr : |r| ≤ 1)
    (x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup X)).subtype) :
    ‖spatialFreeGroupRadial (X := X) α r x‖ ≤ ‖x‖ := by
  exact (spatialSymbolMultiplier_norm_le α (freeGroupRadialSymbol (X := X) r) 1
    (spatialFreeGroupRadial_polynomial_bound α hα r hr) x).trans_eq (one_mul _)

include hα in
lemma spatialFreeGroupRadial_generator (r : ℝ) (hr : |r| ≤ 1) (a : A) (g : FreeGroup X) :
    spatialFreeGroupRadial (X := X) α r
      (spatialCompletionMap α (reducedGroupAlgebra (FreeGroup X)).subtype
        (a ⊗ₜ[ℂ] (reducedGroupUnitary (FreeGroup X) g : reducedGroupAlgebra (FreeGroup X)))) =
    ((r ^ g.toWord.length : ℝ) : ℂ) •
      spatialCompletionMap α (reducedGroupAlgebra (FreeGroup X)).subtype
        (a ⊗ₜ[ℂ] (reducedGroupUnitary (FreeGroup X) g : reducedGroupAlgebra (FreeGroup X))) :=
  spatialSymbolMultiplier_generator α _ 1 (spatialFreeGroupRadial_polynomial_bound α hα r hr) a g

include hα in
lemma spatialFreeGroupRadial_fourier (r : ℝ) (hr : |r| ≤ 1) (g : FreeGroup X)
    (x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup X)).subtype) :
    spatialGroupFourier α g (spatialFreeGroupRadial (X := X) α r x) =
      ((r ^ g.toWord.length : ℝ) : ℂ) • spatialGroupFourier α g x :=
  spatialSymbolMultiplier_fourier α hα _ 1 (spatialFreeGroupRadial_polynomial_bound α hα r hr) g x

include hα in

theorem spatialFreeGroupRadial_tendsto (r : ℕ → ℝ) (hr : ∀ n, |r n| ≤ 1)
    (hlim : Tendsto r atTop (nhds 1))
    (x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup X)).subtype) :
    Tendsto (fun n => spatialFreeGroupRadial (X := X) α (r n) x) atTop (nhds x) := by
  apply spatialSymbolMultiplier_tendsto α _ 1
    (fun n => spatialFreeGroupRadial_polynomial_bound α hα (r n) (hr n))
  intro g
  simpa only [Function.comp_def, freeGroupRadialSymbol, Complex.ofReal_pow, one_pow, Complex.ofReal_one] using
    (Complex.continuous_ofReal.tendsto _).comp (hlim.pow g.toWord.length)
end CuntzPureness

end

end OAI
