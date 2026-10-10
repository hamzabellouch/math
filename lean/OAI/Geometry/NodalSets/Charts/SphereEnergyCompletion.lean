import Mathlib.Analysis.InnerProductSpace.Completion
import OAI.Geometry.NodalSets.Charts.SphereEnergyInnerProduct

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff
noncomputable section

structure SphereEnergyData where
  tensor : IntrinsicTensor
  smooth : IntrinsicTensorSmooth tensor
  symm : ∀ x alpha beta, tensor x alpha beta = tensor x beta alpha
  pos : ∀ x alpha, alpha ≠ 0 → 0 < tensor x alpha alpha
  density : Base → ℝ
  continuous : Continuous density
  positive : ∀ x, 0 < density x

def SphereEnergySmooth (_d : SphereEnergyData) : Type := sphereSmoothFunctions

namespace SphereEnergySmooth
variable (d : SphereEnergyData)
instance instAddCommGroup : AddCommGroup (SphereEnergySmooth d) := inferInstanceAs (AddCommGroup sphereSmoothFunctions)
instance instModule : Module ℝ (SphereEnergySmooth d) := inferInstanceAs (Module ℝ sphereSmoothFunctions)
instance instInnerCore : InnerProductSpace.Core ℝ (SphereEnergySmooth d) :=
  sphereEnergyInnerCore d.tensor d.smooth d.symm d.pos d.density d.continuous d.positive
instance instNormedAddCommGroup : NormedAddCommGroup (SphereEnergySmooth d) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
instance instInnerProductSpace : InnerProductSpace ℝ (SphereEnergySmooth d) :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ (SphereEnergySmooth d))

def toSmooth (u : SphereEnergySmooth d) : sphereSmoothFunctions := u

theorem norm_sq (u : SphereEnergySmooth d) :
    ‖u‖^2 = sphereWeightedPairing d.density (toSmooth d u) (toSmooth d u) +
      sphereDirichletForm d.tensor (toSmooth d u) (toSmooth d u) := by
  exact (real_inner_self_eq_norm_sq u).symm

end SphereEnergySmooth

abbrev SphereEnergyHilbert (d : SphereEnergyData) := UniformSpace.Completion (SphereEnergySmooth d)

def sphereEnergyToCompletion (d : SphereEnergyData) :
    SphereEnergySmooth d →ₗᵢ[ℝ] SphereEnergyHilbert d := UniformSpace.Completion.toComplₗᵢ

theorem sphereEnergyToCompletion_dense (d : SphereEnergyData) :
    DenseRange (sphereEnergyToCompletion d) := UniformSpace.Completion.denseRange_coe

end
end Yau.Target

end OAI
