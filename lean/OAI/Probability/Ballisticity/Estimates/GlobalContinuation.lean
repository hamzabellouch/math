import Mathlib
import OAI.Probability.Ballisticity.Estimates.GlobalProfile

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma globalEndpointProfile_supported {d : ℕ} (e : Direction d) (k : ℕ) (ω : Environment d) :
    ∀ᵐ x ∂globalEndpointProfile e k ω, signedHeight e x=k := by
  apply normalizeOr_ae
  · simpa [variableHitKernel,signedHeight] using
      coordinate_hitKernel_supported e (0:Lattice d) k ω
  · apply (ae_dirac_iff (Set.to_countable _).measurableSet).mpr
    have hh := signedHeight_zsmul_step e (k:ℤ)
    simpa only [natCast_zsmul] using hh

lemma globalHorizontalProfile_lift {d : ℕ} (e : Direction d) (k : ℕ) (ω : Environment d) :
    (globalHorizontalProfile e k ω).map (horizontalLift e k)=globalEndpointProfile e k ω := by
  rw [globalHorizontalProfile,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  calc
    _ = (globalEndpointProfile e k ω).map id := by
      apply Measure.map_congr
      filter_upwards [globalEndpointProfile_supported e k ω] with x hx
      dsimp only [Function.comp_def,id_eq]
      rw [←hx,horizontalLift_projection]
    _ = _ := Measure.map_id

lemma globalEndpointProfile_continuation {d : ℕ} (e : Direction d) (k m : ℕ) (ω : Environment d)
    (hk : crossingQuenched (realPosition (step e)) 0 k ω≠0) (U : Set (Lattice d)) :
    (∫⁻ x, variableHitKernel (realPosition (step e)) m (ω,x) U ∂globalEndpointProfile e k ω) ≤
      (crossingQuenched (realPosition (step e)) 0 (k+m) ω /
        crossingQuenched (realPosition (step e)) 0 k ω)*globalEndpointProfile e (k+m) ω U := by
  have ha : crossingQuenched (realPosition (step e)) 0 k ω≠⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one
  apply (ENNReal.mul_le_mul_iff_right hk ha).mp
  rw [←mul_assoc,ENNReal.mul_div_cancel hk ha]
  have hh := coordinate_raw_kernel_comp_le e k m ω 0 U
  simp only [←Nat.cast_add] at hh ⊢
  change (∫⁻ x, variableHitKernel (realPosition (step e)) m (ω,x) U
    ∂variableHitKernel (realPosition (step e)) k (ω,0)) ≤
      variableHitKernel (realPosition (step e)) (k+m) (ω,0) U at hh
  rw [←globalEndpointProfile_mass e k ω,lintegral_smul_measure,
    ←globalEndpointProfile_mass e (k+m) ω,Measure.smul_apply,smul_eq_mul] at hh
  exact hh

lemma globalHorizontalProfile_continuation {d : ℕ} (e : Direction d) (k m : ℕ) (ω : Environment d)
    (hk : crossingQuenched (realPosition (step e)) 0 k ω≠0) (U : Set (HorizontalSpace e)) :
    (∫⁻ z, variableHitKernel (realPosition (step e)) m (ω,horizontalLift e k z)
      (horizontalProjection e ⁻¹' U) ∂globalHorizontalProfile e k ω) ≤
      (crossingQuenched (realPosition (step e)) 0 (k+m) ω /
        crossingQuenched (realPosition (step e)) 0 k ω)*globalHorizontalProfile e (k+m) ω U := by
  have hh := globalEndpointProfile_continuation e k m ω hk (horizontalProjection e ⁻¹' U)
  rw [←globalHorizontalProfile_lift e k ω,
    lintegral_map (measurable_of_countable _) (measurable_of_countable _)] at hh
  simpa only [globalHorizontalProfile,Measure.map_apply (measurable_of_countable _) (Set.to_countable U).measurableSet] using hh

end DirectionalTransience

end

end OAI
