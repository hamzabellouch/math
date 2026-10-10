import OAI.MeasureTheory.Falconer.Radial.RadialCollisionMass
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! # Threshold deletion for the full conditional radial collision mass -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radial_collision_pair_integral (μ ν : Measure (Space d))
    [SFinite μ] [SFinite ν] (G : Set (Space d × Space d)) (hG : MeasurableSet G) (δ : ℝ) :
    (∫⁻ p in G, radialCollisionMass μ δ p ∂μ.prod ν) =
      ∫⁻ z, (∫⁻ x in {x | (z,x) ∈ G}, radialCollisionMass μ δ (z,x) ∂ν) ∂μ := by
  rw [← lintegral_indicator hG,lintegral_prod _
    ((radialCollisionMass_measurable μ δ).indicator hG).aemeasurable]
  apply lintegral_congr
  intro z
  have hGz : MeasurableSet {x : Space d | (z,x) ∈ G} :=
    hG.preimage (measurable_const.prodMk measurable_id)
  rw [← lintegral_indicator hGz]
  rfl

theorem radial_collision_bad_mass (μ ν : Measure (Space d))
    [SFinite μ] [SFinite ν] (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (δ : ℝ) {F C : ℝ≥0∞} (hF : F ≠ 0) (hFtop : F ≠ ∞)
    (hmean : ∀ᵐ z ∂μ, (∫⁻ x in {x | (z,x) ∈ G}, radialCollisionMass μ δ (z,x) ∂ν) ≤ C) :
    (μ.prod ν) (G ∩ {p | F < radialCollisionMass μ δ p}) ≤ C*μ univ/F := by
  have hmeas := radialCollisionMass_measurable μ δ
  have htotal : (∫⁻ p in G, radialCollisionMass μ δ p ∂μ.prod ν) ≤ C*μ univ := by
    rw [radial_collision_pair_integral μ ν G hG δ]
    exact (lintegral_mono_ae hmean).trans_eq (lintegral_const C)
  have hm : ((μ.prod ν).restrict G) {p | F ≤ radialCollisionMass μ δ p} ≤
      (∫⁻ p in G, radialCollisionMass μ δ p ∂μ.prod ν)/F :=
    meas_ge_le_lintegral_div hmeas.aemeasurable hF hFtop
  calc
    _ = ((μ.prod ν).restrict G) {p | F < radialCollisionMass μ δ p} := by
      rw [Measure.restrict_apply (measurableSet_lt measurable_const hmeas),inter_comm]
    _ ≤ ((μ.prod ν).restrict G) {p | F ≤ radialCollisionMass μ δ p} :=
      measure_mono (fun p hp => show F ≤ radialCollisionMass μ δ p from
        (show F < radialCollisionMass μ δ p from hp).le)
    _ ≤ (∫⁻ p in G, radialCollisionMass μ δ p ∂μ.prod ν)/F := hm
    _ ≤ _ := ENNReal.div_le_div_right htotal F

theorem radial_collision_pruning (μ ν : Measure (Space d))
    [SFinite μ] [SFinite ν] (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (δ : ℝ) {F C : ℝ≥0∞} (hF : F ≠ 0) (hFtop : F ≠ ∞)
    (hmean : ∀ᵐ z ∂μ, (∫⁻ x in {x | (z,x) ∈ G}, radialCollisionMass μ δ (z,x) ∂ν) ≤ C) :
    ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
      (μ.prod ν) (G \ H) ≤ C*μ univ/F ∧ ∀ p ∈ H, radialCollisionMass μ δ p ≤ F := by
  let H := G ∩ {p | radialCollisionMass μ δ p ≤ F}
  refine ⟨H,hG.inter (measurableSet_le (radialCollisionMass_measurable μ δ) measurable_const),
    inter_subset_left,?_,fun _ hp => hp.2⟩
  have he : G \ H = G ∩ {p | F < radialCollisionMass μ δ p} := by
    ext p
    simp only [H,mem_sdiff,mem_inter_iff,mem_ofPred_eq,not_and,not_le]
    tauto
  rw [he]
  exact radial_collision_bad_mass μ ν G hG δ hF hFtop hmean

end Falconer

end OAI
