import OAI.MeasureTheory.Falconer.Estimates.ChargedPlane

namespace OAI

/-! # The charged-plane alternative by induction on the ambient dimension

The affine plane has strictly smaller dimension than the original odd ambient
space. The lower-dimensional distance theorem therefore applies to the
charged-plane alternative in the dimension induction.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d n : ℕ}

theorem distance_in_affine_plane_of_lower_dimensions
    (hmain : ∀ k : ℕ, k < d → 2 ≤ k → ∀ K : Set (Space k), IsCompact K →
      (k : ℝ≥0∞)/2 < dimH K → 0 < volume (distanceSet K))
    (μ : ProbabilityMeasure (Space d)) (hK : IsCompact (μ : Measure (Space d)).support)
    (V : Submodule ℝ (Space d)) (hn : Module.finrank ℝ V = n) (hnlt : n < d) (p : Space d)
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
  have hhalf : (n : ℝ≥0∞)/2 = ENNReal.ofReal ((n:ℝ)/2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num),ENNReal.ofReal_natCast]
    norm_num
  have hdim : (n : ℝ≥0∞)/2 < dimH (ν : Measure (Space n)).support := by
    rw [hhalf]
    apply lt_of_lt_of_le _ (frostman_dimension_lower ν hs0 hC hfrostν)
    apply ENNReal.ofReal_lt_ofReal_iff hs0 |>.mpr
    linarith
  apply positive_distance_of_isometric_model (affineSliceModel_isometry V hn p) _
    (hmain n hnlt hn2 _ hKν hdim)
  rintro _ ⟨y,hy,rfl⟩
  obtain ⟨x,hx,rfl⟩ := hsub hy
  simpa only [P,affineSliceModel_map V hn p x (hsplane hx)] using hx


theorem charged_plane_distance_of_lower_dimensions
    (hmain : ∀ k : ℕ, k < d → 2 ≤ k → ∀ K : Set (Space k), IsCompact K →
      (k : ℝ≥0∞)/2 < dimH K → 0 < volume (distanceSet K))
    (μ : ProbabilityMeasure (Space d)) (hK : IsCompact (μ : Measure (Space d)).support)
    (V : Submodule ℝ (Space d)) (hVlt : Module.finrank ℝ V < d) (p : Space d)
    (hcharge : 0 < (μ : Measure (Space d)) {x | x-p ∈ V})
    {s C : ℝ} (hs : ((Module.finrank ℝ V : ℝ)+1)/2 < s) (hC : 0 < C)
    (hfrost : FrostmanBallBound (μ : Measure (Space d)) s C) :
    0 < volume (distanceSet (μ : Measure (Space d)).support) := by
  let A : Set (Space d) := {x | x-p ∈ V}
  have hA : IsClosed A :=
    V.closed_of_finiteDimensional.preimage (continuous_id.sub continuous_const)
  let ν := positiveRestriction μ A hcharge
  have hdom : (ν : Measure (Space d)) ≪ (μ : Measure (Space d)) :=
    positiveRestriction_absolutelyContinuous μ A hcharge
  have hsupp : (ν : Measure (Space d)).support ⊆ (μ : Measure (Space d)).support :=
    hdom.support_mono
  have hKν : IsCompact (ν : Measure (Space d)).support :=
    hK.of_isClosed_subset Measure.isClosed_support hsupp
  have hplane : (ν : Measure (Space d)) Aᶜ = 0 := by
    change (positiveRestriction μ A hcharge : Measure (Space d)) Aᶜ = 0
    rw [positiveRestriction_eq,Measure.smul_apply,Measure.restrict_apply hA.measurableSet.compl,
      compl_inter_self,measure_empty,smul_zero]
  have hCν : 0 < ((μ : Measure (Space d)) A).toReal⁻¹*C :=
    mul_pos (inv_pos.mpr (ENNReal.toReal_pos hcharge.ne' (measure_ne_top _ _))) hC
  have hfrostν : FrostmanBallBound (ν : Measure (Space d)) s
      (((μ : Measure (Space d)) A).toReal⁻¹*C) := by
    have hid := positiveRestriction_projected_frostman μ A hcharge
      (ContinuousLinearMap.id ℝ (Space d)) (by simpa using hfrost)
    simpa using hid
  have hdist := distance_in_affine_plane_of_lower_dimensions hmain ν hKν V rfl hVlt p
    hplane hs hCν hfrostν
  exact hdist.trans_le (measure_mono (distanceSet_mono hsupp))


end Falconer

end OAI
