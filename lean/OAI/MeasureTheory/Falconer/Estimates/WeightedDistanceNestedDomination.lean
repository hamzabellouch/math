import OAI.MeasureTheory.Falconer.Estimates.WeightedDistanceNestedSupport

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

theorem weightedDistance_le_nested (d : PositiveDistanceData) [SFinite d.ρ]
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) (v : ℕ)
    (hgood : ∀ᵐ z ∂d.cellPair, d.spatialWeight z ≠ 0 →
      z ∈ ({d with t := v,i := d.i+1} : PositiveDistanceData).good) :
    d.weightedDistance ≤ ENNReal.ofReal (d.levelMass^(-2:ℤ)) •
      ({d with t := v,i := d.i+1} : PositiveDistanceData).distance := by
  let e : PositiveDistanceData := {d with t := v,i := d.i+1}
  have hp : d.weightedPair ≤ ENNReal.ofReal (d.levelMass^(-2:ℤ)) • e.pair := by
    change d.weightedPair ≤ ENNReal.ofReal (d.levelMass^(-2:ℤ)) • d.cellPair.restrict e.good
    rw [← withDensity_const,← withDensity_indicator e.measurable_good]
    apply withDensity_mono
    filter_upwards [d.ae_cellPair_mem,hgood] with z hz hg
    by_cases hw : d.spatialWeight z = 0
    · simp only [hw,mul_zero,ENNReal.ofReal_zero]
      exact zero_le
    · rw [Set.indicator_of_mem (hg hw)]
      exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (by positivity)
        (d.spatialWeight_le_one hQ hs hz.1 hz.2))
  have h := Measure.map_mono hp (continuous_fst.dist continuous_snd).measurable
  simpa only [weightedDistance,distance,
    Measure.map_smul _ (continuous_fst.dist continuous_snd).measurable.aemeasurable] using h

end PositiveDistanceData

theorem uniform_weighted_distance_nested_domination {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ (d : PositiveDistanceData) [IsFiniteMeasure d.ρ],
      N₀ ≤ d.N → d.sig = sig → d.J = J → d.Q.side = 1 →
      d.StronglySeparated → d.ρ d.Q.carrierᶜ = 0 → 0 < d.q → d.t ≤ d.N →
      ∀ v ≤ d.t, d.weightedDistance ≤ ENNReal.ofReal (d.levelMass^(-2:ℤ)) •
        ({d with t := v,i := d.i+1} : PositiveDistanceData).distance := by
  obtain ⟨N₀,h₀⟩ := uniform_weighted_distance_nested_support hsig hJ
  refine ⟨N₀,?_⟩
  intro d _ hN hsig' hJ' hQ hs hcarry hq ht v hv
  exact d.weightedDistance_le_nested (hQ.symm ▸ zero_lt_one) hs v
    (h₀ d hN hsig' hJ' hQ hcarry hq ht v hv)

end PlanarFalconer

end OAI
