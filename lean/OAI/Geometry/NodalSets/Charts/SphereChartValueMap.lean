import OAI.Geometry.NodalSets.Charts.SphereChartDerivativeMap

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry
noncomputable section
local instance sphereChartValueMapMeasurable : MeasurableSpace Base := borel Base
local instance sphereChartValueMapBorel : BorelSpace Base := ⟨rfl⟩

theorem sphereChartValue_memLp (d : SphereEnergyData) (p : Base) (f : SphereWeightedL2 d) :
    MemLp (fun x ↦ f (sphereChartCoordMap p x)) 2 (volume.restrict (realFinCube 4)) := by
  obtain ⟨_,_,hb⟩ := sphereWeightedL2_compact_chart_bound d p (realFinCube_isCompact 4)
  exact (hb f).1

def sphereChartValueLinear (d : SphereEnergyData) (p : Base) :
    SphereWeightedL2 d →ₗ[ℝ] SphereChartCubeL2 where
  toFun f := (sphereChartValue_memLp d p f).toLp (fun x ↦ f (sphereChartCoordMap p x))
  map_add' f g := by
    have h := (sphereWeightedMeasure_ae_chart_iff d p (fun x ↦ (f+g) x=f x+g x)).mp (Lp.coeFn_add f g)
    exact (MemLp.toLp_congr _ _ (ae_restrict_of_ae h)).trans
      (MemLp.toLp_add (sphereChartValue_memLp d p f) (sphereChartValue_memLp d p g))
  map_smul' t f := by
    have h := (sphereWeightedMeasure_ae_chart_iff d p (fun x ↦ (t • f) x=t*f x)).mp (Lp.coeFn_smul t f)
    exact (MemLp.toLp_congr _ _ (ae_restrict_of_ae h)).trans
      (MemLp.toLp_const_smul t (sphereChartValue_memLp d p f))

theorem sphereChartValueLinear_bound (d : SphereEnergyData) (p : Base) :
    ∃ C > 0, ∀ f : SphereWeightedL2 d, ‖sphereChartValueLinear d p f‖ ≤ C*‖f‖ := by
  obtain ⟨C,hC,hb⟩ := sphereWeightedL2_compact_chart_bound d p (realFinCube_isCompact 4)
  refine ⟨Real.sqrt C,Real.sqrt_pos.mpr hC,?_⟩
  intro f
  have hn : ‖sphereChartValueLinear d p f‖^2 = ∫ x in realFinCube 4, (f (sphereChartCoordMap p x))^2 :=
    Yau.real_toLp_norm_sq _ (sphereChartValue_memLp d p f)
  have hs : (Real.sqrt C*‖f‖)^2=C*‖f‖^2 := by rw [mul_pow,Real.sq_sqrt hC.le]
  nlinarith [(hb f).2,norm_nonneg (sphereChartValueLinear d p f),
    mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg f)]

def sphereChartValueMap (d : SphereEnergyData) (p : Base) :
    SphereWeightedL2 d →L[ℝ] SphereChartCubeL2 :=
  (sphereChartValueLinear d p).mkContinuous
    (sphereChartValueLinear_bound d p).choose (sphereChartValueLinear_bound d p).choose_spec.2

theorem sphereChartValueMap_ae (d : SphereEnergyData) (p : Base) (f : SphereWeightedL2 d) :
    (sphereChartValueMap d p f : Yau.Jets.Coord → ℝ) =ᵐ[volume.restrict (realFinCube 4)]
      (fun x ↦ f (sphereChartCoordMap p x)) := (sphereChartValue_memLp d p f).coeFn_toLp

theorem sphereChartValueMap_coe_ae (d : SphereEnergyData) (p : Base) (u : SphereEnergySmooth d) :
    (sphereChartValueMap d p (sphereEnergyL2Map d (sphereEnergyToCompletion d u)) : Yau.Jets.Coord → ℝ)
      =ᵐ[volume.restrict (realFinCube 4)]
      (fun x ↦ (SphereEnergySmooth.toSmooth d u : Base → ℝ) (sphereChartCoordMap p x)) := by
  rw [sphereEnergyL2Map_coe]
  apply (sphereChartValueMap_ae d p (sphereEnergyL2Linear d u)).trans
  apply ae_restrict_of_ae
  apply (sphereWeightedMeasure_ae_chart_iff d p (fun x ↦ (sphereEnergyL2Linear d u) x =
    (SphereEnergySmooth.toSmooth d u : Base → ℝ) x)).mp
  exact (sphereWeighted_memLp d.density d.continuous (fun x ↦ (d.positive x).le)
    (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u).property.continuous).coeFn_toLp

end
end Yau.Target

end OAI
