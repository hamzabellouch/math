import OAI.Geometry.NodalSets.Charts.SphereIndexedIntrinsic
import OAI.Geometry.NodalSets.Spectral.SphereVariationalResolvent

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory Filter
open scoped ContDiff Topology
noncomputable section
local instance sphereContinuousRegularityMeasurable : MeasurableSpace Base := borel Base
local instance sphereContinuousRegularityBorel : BorelSpace Base := ⟨rfl⟩

lemma sphere_continuous_eq_of_weighted_ae (d : SphereEnergyData) (u v : Base → ℝ)
    (hu : Continuous u) (hv : Continuous v)
    (ha : u =ᵐ[sphereWeightedMeasure d.density] v) : u=v := by
  let := sphereReferenceMeasure_openPos
  exact Measure.eq_of_ae_eq ((sphereWeightedMeasure_ae_iff d _).mp ha) hu hv

theorem sphere_variational_continuous_regularity
    (d : SphereEnergyData) (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (z : SphereEnergyHilbert d) (lam : ℝ)
    (v : Base → ℝ) (hv : Continuous v) (hne : v ≠ 0)
    (ha : v =ᵐ[sphereWeightedMeasure d.density] (sphereEnergyL2Map d z : Base → ℝ))
    (he : ∀ w : SphereEnergyHilbert d,
      sphereCompletedDirichlet d z w = lam * inner ℝ (sphereEnergyL2Map d z) (sphereEnergyL2Map d w)) :
    ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧
      ∀ p y, -intrinsicWeightedChartOperator d.tensor d.density v p y =
        lam * v ((extChartAt (𝓡 4) p).symm y) := by
  have hmapne : sphereEnergyL2Map d z ≠ 0 := by
    intro hz
    apply hne
    apply sphere_continuous_eq_of_weighted_ae d v 0 hv continuous_const
    rw [hz] at ha
    exact ha.trans (Lp.coeFn_zero ℝ 2 (sphereWeightedMeasure d.density))
  have hlam : 0 < lam+1 := by
    linarith [sphere_variational_eigenvalue_nonneg d lam z hmapne he]
  have hres := (sphere_variational_eigen_to_resolvent d lam z hmapne he).2
  obtain ⟨u,hu,hua,_⟩ := sphere_eigen_global_representative d
    (fun p ↦ (hd.comp (sphereChartCoordMap_smooth p)).contDiff)
    (lam+1)⁻¹ (inv_ne_zero hlam.ne') (sphereEnergyL2Map d z) hres
  have huv : u=v := sphere_continuous_eq_of_weighted_ae d u v hu.continuous hv (hua.trans ha.symm)
  subst u
  let w : SphereEnergySmooth d := (⟨v,hu⟩ : sphereSmoothFunctions)
  have hL : sphereEnergyL2Linear d w=sphereEnergyL2Map d z := by
    apply Lp.ext
    exact (sphereWeighted_memLp d.density d.continuous (fun x ↦ (d.positive x).le)
      v hu.continuous).coeFn_toLp.trans ha
  refine ⟨hu,?_⟩
  have hp := sphere_smooth_resolvent_to_intrinsic d w (lam+1)⁻¹ (inv_ne_zero hlam.ne')
    (by rw [hL]; exact hres)
  simpa only [inv_inv,add_sub_cancel_right,w,SphereEnergySmooth.toSmooth] using hp

end
end Yau.Target

end OAI
