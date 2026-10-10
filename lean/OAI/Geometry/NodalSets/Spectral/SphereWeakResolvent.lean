import Mathlib.Analysis.InnerProductSpace.Adjoint
import OAI.Geometry.NodalSets.Charts.SphereEnergyL2Compact
import OAI.Geometry.NodalSets.Charts.SphereSmoothL2Density

namespace OAI

namespace Yau.Target
open MeasureTheory Filter
open scoped InnerProduct
noncomputable section
local instance sphereWeakResolventMeasurable : MeasurableSpace Base := borel Base
local instance sphereWeakResolventBorel : BorelSpace Base := ⟨rfl⟩

def sphereCompletedDirichlet (d : SphereEnergyData) (u v : SphereEnergyHilbert d) : ℝ :=
  inner ℝ u v-inner ℝ (sphereEnergyL2Map d u) (sphereEnergyL2Map d v)

theorem sphereCompletedDirichlet_coe (d : SphereEnergyData) (u v : SphereEnergySmooth d) :
    sphereCompletedDirichlet d (sphereEnergyToCompletion d u) (sphereEnergyToCompletion d v) =
      sphereDirichletForm d.tensor (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d v) := by
  rw [sphereCompletedDirichlet,sphereEnergyL2Map_coe,sphereEnergyL2Map_coe]
  have hinner : inner ℝ (sphereEnergyL2Linear d u) (sphereEnergyL2Linear d v) =
      sphereWeightedPairing d.density (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d v) :=
    sphereWeightedToLp_inner d.density d.continuous (fun x ↦ (d.positive x).le) _ _
      (SphereEnergySmooth.toSmooth d u).property.continuous (SphereEnergySmooth.toSmooth d v).property.continuous
  rw [hinner,(sphereEnergyToCompletion d).inner_map_map]
  change (sphereWeightedPairing d.density (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d v)+
    sphereDirichletForm d.tensor (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d v))-
    sphereWeightedPairing d.density (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d v) = _
  ring

theorem sphereCompletedDirichlet_nonneg (d : SphereEnergyData) (u : SphereEnergyHilbert d) :
    0 ≤ sphereCompletedDirichlet d u u := by
  rw [sphereCompletedDirichlet,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  nlinarith [sphereEnergyL2Map_apply_norm_le d u,norm_nonneg u,norm_nonneg (sphereEnergyL2Map d u)]

def sphereWeakSolution (d : SphereEnergyData) : SphereWeightedL2 d →L[ℝ] SphereEnergyHilbert d :=
  (sphereEnergyL2Map d).adjoint

theorem sphereWeakSolution_spec (d : SphereEnergyData) (f : SphereWeightedL2 d) (v : SphereEnergyHilbert d) :
    inner ℝ (sphereWeakSolution d f) v = inner ℝ f (sphereEnergyL2Map d v) :=
  (sphereEnergyL2Map d).adjoint_inner_left v f

theorem sphereWeakSolution_unique (d : SphereEnergyData) (f : SphereWeightedL2 d) (u : SphereEnergyHilbert d)
    (hu : ∀ v, inner ℝ u v = inner ℝ f (sphereEnergyL2Map d v)) : u = sphereWeakSolution d f := by
  apply ext_inner_right ℝ
  intro v
  exact (hu v).trans (sphereWeakSolution_spec d f v).symm

theorem sphereWeakSolution_eq_zero_iff (d : SphereEnergyData) (f : SphereWeightedL2 d) :
    sphereWeakSolution d f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    have hclosed : IsClosed {v : SphereWeightedL2 d | inner ℝ f v = 0} :=
      isClosed_eq (by fun_prop) continuous_const
    exact (sphereEnergyL2Map_dense d).induction_on (p := fun v ↦ inner ℝ f v = 0) f hclosed (fun u ↦ by
      rw [← sphereWeakSolution_spec,hf,inner_zero_left])
  · rintro rfl
    exact map_zero _

def sphereL2Resolvent (d : SphereEnergyData) : SphereWeightedL2 d →L[ℝ] SphereWeightedL2 d :=
  (sphereEnergyL2Map d).comp (sphereWeakSolution d)

theorem sphereL2Resolvent_compact (d : SphereEnergyData) : IsCompactOperator (sphereL2Resolvent d) :=
  (sphereEnergyL2Map_compact d).comp_clm (sphereWeakSolution d)

theorem sphereL2Resolvent_inner (d : SphereEnergyData) (f g : SphereWeightedL2 d) :
    inner ℝ (sphereL2Resolvent d f) g = inner ℝ (sphereWeakSolution d f) (sphereWeakSolution d g) := by
  exact ((sphereEnergyL2Map d).adjoint_inner_right (sphereWeakSolution d f) g).symm

theorem sphereL2Resolvent_symmetric (d : SphereEnergyData) : (sphereL2Resolvent d).IsSymmetric := by
  intro f g
  change inner ℝ (sphereL2Resolvent d f) g = inner ℝ f (sphereL2Resolvent d g)
  calc
    _ = inner ℝ (sphereWeakSolution d f) (sphereWeakSolution d g) := sphereL2Resolvent_inner d f g
    _ = inner ℝ (sphereWeakSolution d g) (sphereWeakSolution d f) := real_inner_comm _ _
    _ = inner ℝ (sphereL2Resolvent d g) f := (sphereL2Resolvent_inner d g f).symm
    _ = _ := real_inner_comm _ _

theorem sphereL2Resolvent_positive (d : SphereEnergyData) (f : SphereWeightedL2 d) (hf : f ≠ 0) :
    0 < inner ℝ (sphereL2Resolvent d f) f := by
  rw [sphereL2Resolvent_inner,real_inner_self_eq_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr (fun h ↦ hf ((sphereWeakSolution_eq_zero_iff d f).mp h)))

theorem sphereL2Resolvent_injective (d : SphereEnergyData) : Function.Injective (sphereL2Resolvent d) := by
  apply (sphereEnergyL2Map d).self_comp_adjoint_injective_iff.mpr
  apply (LinearMap.ker_eq_bot).mp
  ext f
  exact sphereWeakSolution_eq_zero_iff d f

theorem sphereL2Resolvent_norm_le (d : SphereEnergyData) : ‖sphereL2Resolvent d‖ ≤ 1 := by
  have ha : ‖sphereWeakSolution d‖ = ‖sphereEnergyL2Map d‖ :=
    ContinuousLinearMap.adjoint.norm_map (sphereEnergyL2Map d)
  have h := ContinuousLinearMap.opNorm_comp_le (sphereEnergyL2Map d) (sphereWeakSolution d)
  rw [ha] at h
  apply h.trans
  nlinarith [sphereEnergyL2Map_norm_le d,norm_nonneg (sphereEnergyL2Map d)]

end
end Yau.Target

end OAI
