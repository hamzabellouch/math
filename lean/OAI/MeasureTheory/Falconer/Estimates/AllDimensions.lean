import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace OAI

/-!
# The all-dimensional Falconer statement and the final measure argument

The Falconer distance conjecture concerns compact subsets of Euclidean
space with Hausdorff dimension greater than half the ambient dimension.
The dimension-independent final measure argument reduces positivity of
the original distance set to absolute continuity of a weighted distance
pushforward.
-/

namespace Falconer
open MeasureTheory Set
open scoped ENNReal

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Original Euclidean distances; auxiliary projections are not used here. -/
def distanceSet {X : Type*} [PseudoMetricSpace X] (E : Set X) : Set ℝ :=
  {r | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}

/-- The Falconer distance conjecture in every ambient dimension at least two. -/
def MainTarget : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : Set (Space d), IsCompact E →
    (d : ℝ≥0∞) / 2 < dimH E → 0 < volume (distanceSet E)

section Geometry
variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

theorem distanceSet_eq_image (E : Set X) :
    distanceSet E = (fun z : X × X => dist z.1 z.2) '' (E ×ˢ E) := by
  ext r
  constructor
  · rintro ⟨x, hx, y, hy, hr⟩
    exact ⟨(x, y), ⟨hx, hy⟩, hr⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, hr⟩
    exact ⟨x, hx, y, hy, hr⟩

theorem distanceSet_isCompact {E : Set X} (hE : IsCompact E) :
    IsCompact (distanceSet E) := by
  rw [distanceSet_eq_image]
  exact (hE.prod hE).image (continuous_fst.dist continuous_snd)

theorem distanceSet_mono {E F : Set X} (h : E ⊆ F) :
    distanceSet E ⊆ distanceSet F := by
  rintro r ⟨x, hx, y, hy, hr⟩
  exact ⟨x, h hx, y, h hy, hr⟩

/-- Isometries, unlike auxiliary orthogonal projections, preserve distances. -/
theorem distanceSet_image_isometry {f : X → Y} (hf : Isometry f) (E : Set X) :
    distanceSet (f '' E) = distanceSet E := by
  ext r
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hr⟩
    exact ⟨x, hx, y, hy, (hf.dist_eq x y).symm.trans hr⟩
  · rintro ⟨x, hx, y, hy, hr⟩
    exact ⟨f x, mem_image_of_mem f hx, f y, mem_image_of_mem f hy,
      (hf.dist_eq x y).trans hr⟩

/-- Transport a distance theorem through an isometric coordinate chart. -/
theorem positive_distance_of_isometric_model {E : Set X} {F : Set Y}
    {f : Y → X} (hf : Isometry f) (hFE : f '' F ⊆ E)
    (hF : 0 < volume (distanceSet F)) : 0 < volume (distanceSet E) := by
  rw [← distanceSet_image_isometry hf F] at hF
  exact hF.trans_le (measure_mono (distanceSet_mono hFE))

end Geometry

section Measures
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

/-- A nonzero absolutely continuous measure carried by a set forces positive
Lebesgue measure. -/
theorem positive_volume_of_carried_measure (D : Set ℝ) (τ : Measure ℝ)
    (hmass : 0 < τ univ) (hcarried : τ Dᶜ = 0) (hac : τ ≪ volume) :
    0 < volume D := by
  by_contra h
  have hzero : volume D = 0 := le_antisymm (not_lt.mp h) bot_le
  have hτ : τ D = 0 := hac hzero
  have hz := measure_union_null hτ hcarried
  have : τ univ = 0 := by simpa only [union_compl_self] using hz
  exact (ne_of_gt hmass) this

/-- The weight in the classical threshold argument, and in the spherical
stationary-phase normalization, is `dist ^ (-(d-1)/2)`. -/
noncomputable def distanceWeight (a : ℝ) (z : X × X) : ℝ≥0∞ :=
  ENNReal.ofReal ((dist z.1 z.2) ^ (-a))

noncomputable def weightedDistance (a : ℝ) (π : Measure (X × X)) : Measure ℝ :=
  Measure.map (fun z => dist z.1 z.2) (π.withDensity (distanceWeight a))

theorem weightedDistance_mass (a : ℝ) (π : Measure (X × X)) :
    weightedDistance a π univ = ∫⁻ z, distanceWeight a z ∂π := by
  rw [weightedDistance, Measure.map_apply (continuous_fst.dist continuous_snd).measurable
    MeasurableSet.univ, Set.preimage_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]

theorem weightedDistance_mass_bounds {a : ℝ} (ha : 0 ≤ a)
    (π : Measure (X × X)) [IsProbabilityMeasure π]
    {dmin dmax : ℝ} (hmin : 0 < dmin)
    (hsep : ∀ᵐ z ∂π, dmin ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ dmax) :
    ENNReal.ofReal (dmax ^ (-a)) ≤ weightedDistance a π univ ∧
      weightedDistance a π univ ≤ ENNReal.ofReal (dmin ^ (-a)) := by
  rw [weightedDistance_mass]
  constructor
  · calc
      ENNReal.ofReal (dmax ^ (-a)) = ∫⁻ _ : X × X,
        ENNReal.ofReal (dmax ^ (-a)) ∂π := by simp
      _ ≤ ∫⁻ z, distanceWeight a z ∂π := by
        apply lintegral_mono_ae
        filter_upwards [hsep] with z hz
        apply ENNReal.ofReal_le_ofReal
        exact Real.rpow_le_rpow_of_nonpos (hmin.trans_le hz.1) hz.2 (neg_nonpos.mpr ha)
  · calc
      (∫⁻ z, distanceWeight a z ∂π) ≤ ∫⁻ _ : X × X,
          ENNReal.ofReal (dmin ^ (-a)) ∂π := by
        apply lintegral_mono_ae
        filter_upwards [hsep] with z hz
        apply ENNReal.ofReal_le_ofReal
        exact Real.rpow_le_rpow_of_nonpos hmin hz.1 (neg_nonpos.mpr ha)
      _ = ENNReal.ofReal (dmin ^ (-a)) := by simp

theorem weightedDistance_positive_finite {a : ℝ} (ha : 0 ≤ a)
    (π : Measure (X × X)) [IsProbabilityMeasure π]
    {dmin dmax : ℝ} (hmin : 0 < dmin) (hmax : 0 < dmax)
    (hsep : ∀ᵐ z ∂π, dmin ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ dmax) :
    0 < weightedDistance a π univ ∧ weightedDistance a π univ < ∞ := by
  obtain ⟨hl, hu⟩ := weightedDistance_mass_bounds ha π hmin hsep
  exact ⟨(ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hmax _)).trans_le hl,
    hu.trans_lt ENNReal.ofReal_lt_top⟩

theorem weightedDistance_carried (a : ℝ) (π : Measure (X × X))
    {E : Set X} (hE : IsCompact E) (hcarrier : π (E ×ˢ E)ᶜ = 0) :
    weightedDistance a π (distanceSet E)ᶜ = 0 := by
  rw [weightedDistance, Measure.map_apply (continuous_fst.dist continuous_snd).measurable
    (distanceSet_isCompact hE).measurableSet.compl]
  apply withDensity_absolutelyContinuous π (distanceWeight a)
  apply measure_mono_null _ hcarrier
  intro z hz hzin
  exact hz ⟨z.1, hzin.1, z.2, hzin.2, rfl⟩

omit [MetricSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem product_carried (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set X) (hμ : μ Eᶜ = 0) (hν : ν Eᶜ = 0) :
    (μ.prod ν) (E ×ˢ E)ᶜ = 0 := by
  have hleft : (μ.prod ν) (Eᶜ ×ˢ (univ : Set X)) = 0 := by
    simp [Measure.prod_prod, hμ]
  have hright : (μ.prod ν) ((univ : Set X) ×ˢ Eᶜ) = 0 := by
    simp [Measure.prod_prod, hν]
  apply measure_mono_null _ (measure_union_null hleft hright)
  intro z hz
  by_cases hx : z.1 ∈ E
  · exact Or.inr ⟨mem_univ _, fun hy => hz ⟨hx, hy⟩⟩
  · exact Or.inl ⟨hx, mem_univ _⟩

/-- The dimension-independent final reduction to absolute continuity of the
original weighted distance pushforward. No Fourier estimate is assumed here. -/
theorem positive_distance_of_weighted_ac {a : ℝ} (ha : 0 ≤ a)
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Set X} (hE : IsCompact E) (hμ : μ Eᶜ = 0) (hν : ν Eᶜ = 0)
    {dmin dmax : ℝ} (hmin : 0 < dmin) (hmax : 0 < dmax)
    (hsep : ∀ᵐ z ∂(μ.prod ν), dmin ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ dmax)
    (hac : weightedDistance a (μ.prod ν) ≪ volume) :
    0 < volume (distanceSet E) := by
  exact positive_volume_of_carried_measure (distanceSet E) (weightedDistance a (μ.prod ν))
    (weightedDistance_positive_finite ha (μ.prod ν) hmin hmax hsep).1
    (weightedDistance_carried a (μ.prod ν) hE (product_carried μ ν E hμ hν)) hac

end Measures
end Falconer

end OAI
