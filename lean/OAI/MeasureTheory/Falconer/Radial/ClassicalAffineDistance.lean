import OAI.MeasureTheory.Falconer.Slicing.AffineSliceCoordinates
import OAI.MeasureTheory.Falconer.Shells.PublishedClassicalDistance
import OAI.MeasureTheory.Falconer.Shells.PositiveRestriction

namespace OAI

/-! # The strict classical threshold on a charged affine plane

Coordinates are used isometrically inside the actual affine plane, so the
conclusion concerns original distances.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d n : ℕ}

theorem frostman_exponent_le_dimension (μ : ProbabilityMeasure (Space n)) {s C : ℝ}
    (hs : 0 < s) (hC : 0 < C) (hfrost : FrostmanBallBound (μ : Measure (Space n)) s C) :
    s ≤ (n:ℝ) := by
  have hu : dimH (univ : Set (Space n)) = (n:ℝ≥0∞) := by
    simp [Real.dimH_univ_eq_finrank,Space]
  have hd := (frostman_dimension_lower μ hs hC hfrost).trans
    ((dimH_mono (subset_univ _)).trans_eq hu)
  have hh := ENNReal.toReal_mono (by simp : (n:ℝ≥0∞) ≠ ∞) hd
  simpa [ENNReal.toReal_ofReal hs.le] using hh

theorem classical_distance_in_affine_plane (hpublished : PublishedClassicalDistance)
    (μ : ProbabilityMeasure (Space d)) (hK : IsCompact (μ : Measure (Space d)).support)
    (V : Submodule ℝ (Space d)) (hn : Module.finrank ℝ V = n) (p : Space d)
    (hplane : (μ : Measure (Space d)) {x | x-p ∈ V}ᶜ = 0)
    {s C : ℝ} (hs : ((n:ℝ)+1)/2 < s) (hC : 0 < C)
    (hfrost : FrostmanBallBound (μ : Measure (Space d)) s C) :
    0 < volume (distanceSet (μ : Measure (Space d)).support) := by
  let P := affineSliceMap V hn p
  let ν := μ.map P
  have hP : Continuous P := affineSliceMap_continuous V hn p
  have hfrostν : FrostmanBallBound (ν : Measure (Space n)) s C :=
    affineSliceMap_frostman (μ : Measure (Space d)) V hn p hplane hfrost
  have hs0 : 0 < s := (by positivity : (0:ℝ) ≤ ((n:ℝ)+1)/2).trans_lt hs
  have hsN := frostman_exponent_le_dimension ν hs0 hC hfrostν
  have hn2 : 2 ≤ n := by
    by_contra hn2
    have hn1 : n ≤ 1 := by omega
    have hn1R : (n:ℝ) ≤ 1 := by exact_mod_cast hn1
    linarith
  have himage := hK.image hP
  have hsub : (ν : Measure (Space n)).support ⊆ P '' (μ : Measure (Space d)).support := by
    apply Measure.support_subset_of_isClosed himage.isClosed
    change (μ : Measure (Space d)).map P (P '' (μ : Measure (Space d)).support)ᶜ = 0
    rw [Measure.map_apply hP.measurable himage.isClosed.measurableSet.compl]
    apply measure_mono_null _ Measure.measure_compl_support
    intro x hx hxS
    exact hx ⟨x,hxS,rfl⟩
  have hKν : IsCompact (ν : Measure (Space n)).support :=
    himage.of_isClosed_subset Measure.isClosed_support hsub
  have hclosed : IsClosed {x : Space d | x-p ∈ V} :=
    V.closed_of_finiteDimensional.preimage (continuous_id.sub continuous_const)
  have hsplane : (μ : Measure (Space d)).support ⊆ {x | x-p ∈ V} :=
    Measure.support_subset_of_isClosed hclosed hplane
  apply positive_distance_of_isometric_model (affineSliceModel_isometry V hn p) _
    (classical_distance_of_frostman hpublished hn2 ν hKν hs hC hfrostν)
  rintro _ ⟨y,hy,rfl⟩
  obtain ⟨x,hx,rfl⟩ := hsub hy
  simpa only [P,affineSliceModel_map V hn p x (hsplane hx)] using hx

end Falconer

end OAI
