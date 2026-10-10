import OAI.MeasureTheory.Falconer.Fourier.DistanceKernelSplitting
import OAI.MeasureTheory.Falconer.Angular.RotatedConeKernel

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem integrable_distanceFormIntegrand (ψ U V : UnitCircle → ℂ)
    (hψ : Measurable ψ) (hU : Measurable U) (hV : Measurable V)
    {P B C : ℝ} (hP : 0 ≤ P) (hB : 0 ≤ B)
    (hp : ∀ dir, ‖ψ dir‖ ≤ P) (hb : ∀ dir, ‖U dir‖ ≤ B)
    (hc : ∀ dir, ‖V dir‖ ≤ C) :
    Integrable (fun dir => ψ dir * U dir * conj (V dir)) sourceArcLength := by
  apply (integrable_const (P*B*C)).mono
  · exact ((hψ.mul hU).mul (Complex.continuous_conj.measurable.comp hV)).aestronglyMeasurable
  · filter_upwards with dir
    rw [norm_mul, norm_mul, Complex.norm_conj]
    exact (mul_le_mul (mul_le_mul (hp dir) (hb dir) (norm_nonneg _) hP)
      (hc dir) (norm_nonneg _) (mul_nonneg hP hB)).trans (le_abs_self _)

theorem sourceDistanceF_retained_add_discarded (ψ χ : UnitCircle → ℂ)
    (U V : ℝ × UnitCircle → ℂ) (r : ℝ)
    (hψ : Measurable ψ) (hχ : Measurable χ)
    (hU : Measurable (fun dir => U (r,dir))) (hV : Measurable (fun dir => V (r,dir)))
    {P B C : ℝ} (hP : 0 ≤ P) (hB : 0 ≤ B)
    (hp : ∀ dir, ‖ψ dir‖ ≤ P) (hχb : ∀ dir, ‖χ dir‖ ≤ 1)
    (hb : ∀ dir, ‖U (r,dir)‖ ≤ B) (hc : ∀ dir, ‖V (r,dir)‖ ≤ C) :
    sourceDistanceF ψ U V r =
      sourceDistanceF (fun dir => ψ dir*(1-χ dir)) U V r +
        sourceDistanceF (fun dir => ψ dir*χ dir) U V r := by
  have hfull := integrable_distanceFormIntegrand ψ _ _ hψ hU hV hP hB hp hb hc
  have hdisc := integrable_distanceFormIntegrand (fun dir => ψ dir*χ dir) _ _
    (hψ.mul hχ) hU hV hP hB
    (fun dir => by
      rw [norm_mul]
      exact (mul_le_mul (hp dir) (hχb dir) (norm_nonneg _) hP).trans_eq (mul_one P)) hb hc
  have he : (fun dir => ψ dir*(1-χ dir)*U (r,dir)*conj (V (r,dir))) =
      fun dir => ψ dir*U (r,dir)*conj (V (r,dir)) -
        (ψ dir*χ dir)*U (r,dir)*conj (V (r,dir)) := by funext dir; ring
  unfold sourceDistanceF
  rw [he, integral_sub hfull hdisc, sub_add_cancel]

theorem sourceDistanceF_discarded_mass_bound (ρ ν : Measure Plane)
    [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (X Y : Set Plane)
    {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (ψ : UnitCircle → ℂ) (b₁ b₂ : Plane → UnitCircle → ℂ) (hψ : Measurable ψ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {P B₁ B₂ ε : ℝ} (hP : 0 ≤ P) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hp : ∀ dir, ‖ψ dir‖ ≤ P) (hb₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁)
    (hb₂ : ∀ y dir, ‖b₂ y dir‖ ≤ B₂) (r : ℝ)
    (he : ∀ x ∈ X, ∀ y ∈ Y, ‖sourceDistanceKernel ψ b₁ b₂ r x y‖ ≤ ε) :
    ‖sourceDistanceF ψ (fun z => sourceAngularTransform ρ X M₁ b₁ z.1 z.2)
      (fun z => sourceAngularTransform ν Y M₂ b₂ z.1 z.2) r‖ ≤
      ε*((ρ X).toReal/M₁)*((ν Y).toReal/M₂) := by
  rw [sourceDistanceF_endpoint_integral ρ ν X Y M₁ M₂ ψ b₁ b₂ hψ h₁ h₂ hP hB₁ hB₂ hp hb₁ hb₂]
  exact normalized_pair_integral_norm_le ρ ν X Y hM₁ hM₂ _ he

theorem rotated_bin_activity_iff (n j : ℕ) (axis : ℝ) (e : UnitCircle) (radius : ℝ) :
    (∃ dir ∈ tsupport (fun dir => circleAngularBin n j (sourceCircleRotate (-axis) dir)),
      dist (sourceCircleRotate axis e) dir < radius) ↔ AngularBinActive n j e radius := by
  have hs := tsupport_comp_eq_preimage (circleAngularBin n j) (sourceCircleRotation (-axis))
  change tsupport (fun dir => circleAngularBin n j (sourceCircleRotate (-axis) dir)) =
    sourceCircleRotate (-axis) ⁻¹' tsupport (circleAngularBin n j) at hs
  rw [hs]
  constructor
  · rintro ⟨dir, hd, he⟩
    refine ⟨sourceCircleRotate (-axis) dir, hd, ?_⟩
    have hh := sourceCircleRotate_dist (-axis) (sourceCircleRotate axis e) dir
    simp only [sourceCircleRotate_add, add_neg_cancel, sourceCircleRotate_zero] at hh
    rwa [hh]
  · rintro ⟨dir, hd, he⟩
    refine ⟨sourceCircleRotate axis dir, ?_, ?_⟩
    · simpa only [mem_preimage, sourceCircleRotate_add, add_neg_cancel, sourceCircleRotate_zero] using hd
    · rwa [sourceCircleRotate_dist]

end PlanarFalconer

end OAI
