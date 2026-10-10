import Mathlib.Analysis.Normed.Operator.Extend
import OAI.Geometry.NodalSets.Charts.SphereEnergyCompletion
import OAI.Geometry.NodalSets.Charts.SphereWeightedL2

namespace OAI

namespace Yau.Target
open MeasureTheory
noncomputable section
local instance sphereEnergyL2MapMeasurable : MeasurableSpace Base := borel Base
local instance sphereEnergyL2MapBorel : BorelSpace Base := ⟨rfl⟩

abbrev SphereWeightedL2 (d : SphereEnergyData) := Lp ℝ 2 (sphereWeightedMeasure d.density)

def sphereEnergyL2Linear (d : SphereEnergyData) : SphereEnergySmooth d →ₗ[ℝ] SphereWeightedL2 d where
  toFun u := sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le)
    (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u).property.continuous
  map_add' u v := by
    exact MemLp.toLp_add
      (sphereWeighted_memLp d.density d.continuous (fun x ↦ (d.positive x).le)
        (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u).property.continuous)
      (sphereWeighted_memLp d.density d.continuous (fun x ↦ (d.positive x).le)
        (SphereEnergySmooth.toSmooth d v) (SphereEnergySmooth.toSmooth d v).property.continuous)
  map_smul' t u := by
    exact MemLp.toLp_const_smul t
      (sphereWeighted_memLp d.density d.continuous (fun x ↦ (d.positive x).le)
        (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u).property.continuous)

theorem sphereEnergyL2Linear_norm_sq (d : SphereEnergyData) (u : SphereEnergySmooth d) :
    ‖sphereEnergyL2Linear d u‖^2 =
      sphereWeightedPairing d.density (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u) :=
  sphereWeightedToLp_norm_sq d.density d.continuous (fun x ↦ (d.positive x).le)
    (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u).property.continuous

theorem sphereEnergyL2Linear_norm_le (d : SphereEnergyData) (u : SphereEnergySmooth d) :
    ‖sphereEnergyL2Linear d u‖ ≤ ‖u‖ := by
  have h := SphereEnergySmooth.norm_sq d u
  have he := sphereDirichletForm_nonneg d.tensor d.pos (SphereEnergySmooth.toSmooth d u)
  have hl := sphereEnergyL2Linear_norm_sq d u
  nlinarith [norm_nonneg u,norm_nonneg (sphereEnergyL2Linear d u)]

def sphereEnergyL2SmoothMap (d : SphereEnergyData) : SphereEnergySmooth d →L[ℝ] SphereWeightedL2 d :=
  (sphereEnergyL2Linear d).mkContinuous 1 (by simpa using sphereEnergyL2Linear_norm_le d)

def sphereEnergyL2Map (d : SphereEnergyData) : SphereEnergyHilbert d →L[ℝ] SphereWeightedL2 d :=
  (sphereEnergyL2Linear d).extendOfNorm (sphereEnergyToCompletion d).toLinearMap

theorem sphereEnergyL2Map_coe (d : SphereEnergyData) (u : SphereEnergySmooth d) :
    sphereEnergyL2Map d (sphereEnergyToCompletion d u) = sphereEnergyL2Linear d u := by
  apply LinearMap.extendOfNorm_eq (sphereEnergyToCompletion_dense d)
  refine ⟨1,fun v ↦ ?_⟩
  simpa using sphereEnergyL2Linear_norm_le d v

theorem sphereEnergyL2Map_norm_le (d : SphereEnergyData) : ‖sphereEnergyL2Map d‖ ≤ 1 := by
  apply LinearMap.opNorm_extendOfNorm_le (sphereEnergyToCompletion_dense d) zero_le_one
  intro u
  simpa using sphereEnergyL2Linear_norm_le d u

theorem sphereEnergyL2Map_apply_norm_le (d : SphereEnergyData) (u : SphereEnergyHilbert d) :
    ‖sphereEnergyL2Map d u‖ ≤ ‖u‖ := by
  have h := (sphereEnergyL2Map d).le_opNorm u
  exact h.trans (by simpa using mul_le_mul_of_nonneg_right (sphereEnergyL2Map_norm_le d) (norm_nonneg u))

theorem sphereEnergyL2Map_unique (d : SphereEnergyData)
    (T : SphereEnergyHilbert d →L[ℝ] SphereWeightedL2 d)
    (hT : ∀ u, T (sphereEnergyToCompletion d u) = sphereEnergyL2Linear d u) :
    T = sphereEnergyL2Map d := by
  apply ContinuousLinearMap.coeFn_injective
  apply (sphereEnergyToCompletion_dense d).equalizer T.continuous (sphereEnergyL2Map d).continuous
  funext u
  exact (hT u).trans (sphereEnergyL2Map_coe d u).symm

end
end Yau.Target

end OAI
