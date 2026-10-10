import OAI.Geometry.ProjectionVolume.PolytopeFront
import OAI.Geometry.ProjectionVolume.Brightness
import OAI.Geometry.ProjectionVolume.ProjectionReconstruction

namespace OAI

universe uι

open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

noncomputable section

namespace Paper092.HPolytope

variable {d : ℕ} {ι : Type uι} [Fintype ι] (P : HPolytope d ι)

theorem velocity_neg (u : Euclidean d) (i : ι) :
    P.velocity (-u) i = -P.velocity u i := by simp [velocity]

private theorem brightness_eq_filtered_sum (u : Euclidean d) (hu : u ≠ 0) :
    brightness P.body u =
      ∑ i, if P.velocity u i < 0 then P.faceArea i * |⟪u, P.normal i⟫| else 0 := by
  classical
  rw [P.brightness_eq_front_sum u hu]
  simp only [face_brightness]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter (fun i => P.velocity u i < 0))
    (by simp) (fun i => P.faceArea i * |⟪u, P.normal i⟫|)).symm

theorem brightness_eq_sum (u : Euclidean d) :
    brightness P.body u = (∑ i, P.faceArea i * |⟪u, P.normal i⟫|) / 2 := by
  classical
  by_cases hu : u = 0
  · simp [hu, brightness]
  have hplus := P.brightness_eq_filtered_sum u hu
  have hminus := P.brightness_eq_filtered_sum (-u) (neg_ne_zero.mpr hu)
  simp only [brightness_neg, velocity_neg, neg_lt_zero, inner_neg_left, abs_neg] at hminus
  have hpoint (i : ι) :
      (if P.velocity u i < 0 then P.faceArea i * |⟪u, P.normal i⟫| else 0) +
        (if 0 < P.velocity u i then P.faceArea i * |⟪u, P.normal i⟫| else 0) =
          P.faceArea i * |⟪u, P.normal i⟫| := by
    rcases lt_trichotomy (P.velocity u i) 0 with hi | hi | hi
    · simp [hi, not_lt_of_gt hi]
    · have hinner : ⟪u, P.normal i⟫ = 0 := by
        simpa only [velocity, neg_eq_zero, real_inner_comm] using hi
      simp [hi, hinner]
    · simp [hi, not_lt_of_gt hi]
  have hsum := congrArg (fun f : ι → ℝ => ∑ i, f i) (funext hpoint)
  simp only [Finset.sum_add_distrib] at hsum
  rw [← hplus, ← hminus] at hsum
  linarith

theorem faceArea_nonneg (i : ι) : 0 ≤ P.faceArea i := ENNReal.toReal_nonneg

theorem facetZonotope_isCompact : IsCompact P.facetZonotope := by
  classical
  exact Finset.sum_induction _ IsCompact (fun _ _ ha hb => ha.add hb)
    isCompact_singleton (fun _ _ => SupportGeometry.isCompact_segment _ _)

theorem facetZonotope_nonempty : P.facetZonotope.Nonempty := by
  classical
  exact Finset.sum_induction _ Set.Nonempty (fun _ _ ha hb => ha.add hb)
    (singleton_nonempty 0) (fun _ _ => ⟨_, left_mem_segment ℝ _ _⟩)

theorem facetZonotope_convex : Convex ℝ P.facetZonotope := by
  classical
  exact Finset.sum_induction _ (Convex ℝ) (fun _ _ ha hb => ha.add hb)
    (convex_singleton 0) (fun _ _ => convex_segment _ _)

theorem facetZonotope_support (u : Euclidean d) :
    SupportGeometry.support P.facetZonotope (innerSL ℝ u) =
      (∑ i, P.faceArea i * |⟪u, P.normal i⟫|) / 2 := by
  classical
  unfold facetZonotope
  rw [SupportGeometry.support_sum _ _
    (fun _ _ => SupportGeometry.isCompact_segment _ _)
    (fun _ _ => ⟨_, left_mem_segment ℝ _ _⟩)]
  have hseg (i : ι) : SupportGeometry.support
      (segment ℝ (-(P.faceArea i / 2) • P.normal i)
        ((P.faceArea i / 2) • P.normal i)) (innerSL ℝ u) =
          P.faceArea i * |⟪u, P.normal i⟫| / 2 := by
    have heq : segment ℝ (-(P.faceArea i / 2) • P.normal i)
        ((P.faceArea i / 2) • P.normal i) =
        segment ℝ (-(1 / 2 : ℝ) • (P.faceArea i • P.normal i))
          ((1 / 2 : ℝ) • (P.faceArea i • P.normal i)) := by
      congr 1 <;> simp only [smul_smul] <;> congr 1 <;> ring
    rw [heq, SupportGeometry.support_centered_segment]
    change |⟪u, P.faceArea i • P.normal i⟫| / 2 = _
    simp only [real_inner_smul_right, abs_mul,
      abs_of_nonneg (P.faceArea_nonneg i)]
  simp only [hseg]
  exact (Finset.sum_div _ _ _).symm

theorem projectionBody_eq_facetZonotope : projectionBody P.body = P.facetZonotope :=
  Paper092.projectionBody_eq_of_brightness_eq_support P.facetZonotope_isCompact
    P.facetZonotope_nonempty P.facetZonotope_convex
    (fun u => (P.brightness_eq_sum u).trans (P.facetZonotope_support u).symm)

theorem projectionBody_support (u : Euclidean d) :
    SupportGeometry.support (projectionBody P.body) (innerSL ℝ u) = brightness P.body u := by
  rw [P.projectionBody_eq_facetZonotope, P.facetZonotope_support, P.brightness_eq_sum]

end Paper092.HPolytope

end

end OAI
