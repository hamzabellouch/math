import OAI.MeasureTheory.Falconer.DistanceSet
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

noncomputable def distanceWeight (z : Plane × Plane) : ℝ≥0∞ :=
  ENNReal.ofReal ((dist z.1 z.2) ^ (-1/2 : ℝ))

noncomputable def weightedDistance (π : Measure (Plane × Plane)) : Measure ℝ :=
  Measure.map (fun z => dist z.1 z.2) (π.withDensity distanceWeight)

theorem weightedDistance_mass (π : Measure (Plane × Plane)) :
    weightedDistance π univ = ∫⁻ z, distanceWeight z ∂π := by
  rw [weightedDistance, Measure.map_apply (continuous_fst.dist continuous_snd).measurable
    MeasurableSet.univ, Set.preimage_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]

theorem weightedDistance_mass_bounds (π : Measure (Plane × Plane)) [IsProbabilityMeasure π]
    {dmin dmax : ℝ} (hmin : 0 < dmin)
    (hsep : ∀ᵐ z ∂π, dmin ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ dmax) :
    ENNReal.ofReal (dmax ^ (-1/2 : ℝ)) ≤ weightedDistance π univ ∧
      weightedDistance π univ ≤ ENNReal.ofReal (dmin ^ (-1/2 : ℝ)) := by
  rw [weightedDistance_mass]
  constructor
  · calc
      ENNReal.ofReal (dmax ^ (-1/2 : ℝ)) = ∫⁻ _ : Plane × Plane,
        ENNReal.ofReal (dmax ^ (-1/2 : ℝ)) ∂π := by simp
      _ ≤ ∫⁻ z, distanceWeight z ∂π := by
        apply lintegral_mono_ae
        filter_upwards [hsep] with z hz
        apply ENNReal.ofReal_le_ofReal
        exact Real.rpow_le_rpow_of_nonpos (hmin.trans_le hz.1) hz.2 (by norm_num)
  · calc
      (∫⁻ z, distanceWeight z ∂π) ≤ ∫⁻ _ : Plane × Plane,
          ENNReal.ofReal (dmin ^ (-1/2 : ℝ)) ∂π := by
        apply lintegral_mono_ae
        filter_upwards [hsep] with z hz
        apply ENNReal.ofReal_le_ofReal
        exact Real.rpow_le_rpow_of_nonpos hmin hz.1 (by norm_num)
      _ = ENNReal.ofReal (dmin ^ (-1/2 : ℝ)) := by simp

theorem weightedDistance_positive_finite (π : Measure (Plane × Plane)) [IsProbabilityMeasure π]
    {dmin dmax : ℝ} (hmin : 0 < dmin) (hmax : 0 < dmax)
    (hsep : ∀ᵐ z ∂π, dmin ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ dmax) :
    0 < weightedDistance π univ ∧ weightedDistance π univ < ∞ := by
  obtain ⟨hl,hu⟩ := weightedDistance_mass_bounds π hmin hsep
  exact ⟨(ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hmax _)).trans_le hl,
    hu.trans_lt ENNReal.ofReal_lt_top⟩

theorem weightedDistance_carried (π : Measure (Plane × Plane))
    {E : Set Plane} (hE : IsCompact E) (hcarrier : π (E ×ˢ E)ᶜ = 0) :
    weightedDistance π (distanceSet E)ᶜ = 0 := by
  rw [weightedDistance, Measure.map_apply (continuous_fst.dist continuous_snd).measurable
    (distanceSet_measurable hE).compl]
  apply withDensity_absolutelyContinuous π distanceWeight
  apply measure_mono_null _ hcarrier
  intro z hz hzin
  exact hz ⟨z.1,hzin.1,z.2,hzin.2,rfl⟩

theorem product_carried (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set Plane) (hμ : μ Eᶜ = 0) (hν : ν Eᶜ = 0) :
    (μ.prod ν) (E ×ˢ E)ᶜ = 0 := by
  have hleft : (μ.prod ν) (Eᶜ ×ˢ (univ : Set Plane)) = 0 := by simp [Measure.prod_prod,hμ]
  have hright : (μ.prod ν) ((univ : Set Plane) ×ˢ Eᶜ) = 0 := by simp [Measure.prod_prod,hν]
  apply measure_mono_null _ (measure_union_null hleft hright)
  intro z hz
  by_cases hx : z.1 ∈ E
  · right
    refine ⟨Set.mem_univ _, ?_⟩
    intro hy
    exact hz ⟨hx,hy⟩
  · left
    exact ⟨hx,Set.mem_univ _⟩

theorem positive_distance_volume_of_weighted_ac (μ ν : Measure Plane)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Set Plane} (hE : IsCompact E) (hμ : μ Eᶜ = 0) (hν : ν Eᶜ = 0)
    {dmin dmax : ℝ} (hmin : 0 < dmin) (hmax : 0 < dmax)
    (hsep : ∀ᵐ z ∂(μ.prod ν), dmin ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ dmax)
    (hac : weightedDistance (μ.prod ν) ≪ volume) : 0 < volume (distanceSet E) := by
  exact distanceSet_positive_of_measure E (weightedDistance (μ.prod ν))
    (weightedDistance_positive_finite (μ.prod ν) hmin hmax hsep).1
    (weightedDistance_carried (μ.prod ν) hE (product_carried μ ν E hμ hν)) hac

end PlanarFalconer

end OAI
