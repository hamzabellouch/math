import OAI.Analysis.Pureness.GroupAlgebra.CauchyFourierIdealApproximation
import OAI.Analysis.Pureness.Tensor.SpatialFourierConvergence

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
local instance cauchyUniformFourierExactnessDecidableEq {X : Type*} : DecidableEq X := Classical.decEq X
open Filter Topology
variable {D H L : Type*}
variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (ht : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (α : T.cauchySequenceAlgebra ht →⋆ₐ[ℂ] (H →L[ℂ] H))
variable (γ : T.CauchyQuotient ht →⋆ₐ[ℂ] (L →L[ℂ] L))
variable (hα : Function.Injective α) (hγ : Function.Injective γ)

lemma cauchyFiniteFourier_eq_spatial (s : Finset (FreeGroup ℕ)) (c : FreeGroup ℕ → ℂ)
    (x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype) :
    T.cauchyFiniteFourier ht α s c x = spatialFiniteFourier (G := FreeGroup ℕ) α s c x :=
  (spatialFiniteFourier_apply α s c x).symm

include hγ in

theorem cauchyTensorKernel_mem_ideal_of_uniform_fourier
    (s : ℕ → Finset (FreeGroup ℕ)) (c : ℕ → FreeGroup ℕ → ℂ) (C : ℝ)
    (hbound : ∀ n x, ‖spatialFiniteFourier (G := FreeGroup ℕ) α (s n) (c n) x‖ ≤ C * ‖x‖)
    (hcoeff : ∀ g, Tendsto (fun n => if g ∈ s n then c n g else 0) atTop (nhds 1))
    (x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype)
    (hx : T.cauchyFreeGroupTensorMap ht α γ hα x = 0) :
    x ∈ (spatialTensorKernelIdeal (T.cauchyQuotientStarHom ht) α
      (reducedGroupAlgebra (FreeGroup ℕ)).subtype).ideal := by
  apply T.cauchyTensorKernel_mem_ideal_of_fourier_tendsto ht α γ hα hγ s c x hx
  simp only [cauchyFiniteFourier_eq_spatial]
  exact spatialFiniteFourier_tendsto_of_uniform_bound α hα s c C hbound hcoeff x
end CuntzPureness.PositiveQuasitrace

end

end OAI
