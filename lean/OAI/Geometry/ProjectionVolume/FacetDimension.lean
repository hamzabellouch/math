import OAI.Geometry.ProjectionVolume.FacetUniqueness
import OAI.Geometry.ProjectionVolume.ProjectionNullity

namespace OAI

universe uι

open Set MeasureTheory
open scoped RealInnerProductSpace Classical Pointwise

noncomputable section

namespace Paper092.HPolytope

variable {d : ℕ} {ι : Type uι} [Fintype ι] (P : HPolytope d ι)

theorem face_finrank_le (i : ι) :
    Module.finrank ℝ (vectorSpan ℝ (P.face i)) ≤ d - 1 := by
  have hn : P.normal i ≠ 0 := by
    intro h
    have := P.normal_unit i
    simp only [h, norm_zero] at this
    norm_num at this
  have h := Submodule.finrank_mono (P.face_vectorSpan_le_normalHyperplane i)
  rwa [normalHyperplane_finrank (P.normal i) hn] at h

theorem face_surface_zero_of_finrank_lt (i : ι)
    (h : Module.finrank ℝ (vectorSpan ℝ (P.face i)) < d - 1) :
    μHE[d - 1] (P.face i) = 0 := by
  have hn : P.normal i ≠ 0 := by
    intro h
    have := P.normal_unit i
    simp only [h, norm_zero] at this
    norm_num at this
  have hz := projectionVolume_eq_zero_of_finrank_lt (P.face i) hn h
  rw [projectionVolume_of_subset_affine_hyperplane (P.normal i) (P.normal i)
    (P.normal_unit i) (P.normal_unit i) (P.offset i) (P.face i) (fun _ hx => hx.2)] at hz
  simpa only [real_inner_self_eq_norm_sq, P.normal_unit, one_pow, abs_one,
    ENNReal.ofReal_one, one_mul] using hz

theorem faceArea_zero_of_not_facet (i : ι)
    (h : ¬ ((P.face i).Nonempty ∧
      Module.finrank ℝ (vectorSpan ℝ (P.face i)) = d - 1)) : P.faceArea i = 0 := by
  by_cases hne : (P.face i).Nonempty
  · have hdim : Module.finrank ℝ (vectorSpan ℝ (P.face i)) ≠ d - 1 :=
      fun heq => h ⟨hne, heq⟩
    rw [faceArea, P.face_surface_zero_of_finrank_lt i (lt_of_le_of_ne (P.face_finrank_le i) hdim),
      ENNReal.toReal_zero]
  · have he : P.face i = ∅ := by
      ext x
      constructor
      · intro hx
        exact (hne ⟨x, hx⟩).elim
      · intro hx
        exact hx.elim
    simp only [faceArea, he, measure_empty, ENNReal.toReal_zero]

theorem brightness_eq_facet_sum (u : Euclidean d) :
    brightness P.body u = (1 / 2 : ℝ) *
      ∑ i ∈ Finset.univ.filter (fun i => (P.face i).Nonempty ∧
        Module.finrank ℝ (vectorSpan ℝ (P.face i)) = d - 1),
        P.faceArea i * |⟪P.normal i, u⟫| := by
  have hsum : (∑ i, P.faceArea i * |⟪u, P.normal i⟫|) =
      ∑ i ∈ Finset.univ.filter (fun i => (P.face i).Nonempty ∧
        Module.finrank ℝ (vectorSpan ℝ (P.face i)) = d - 1),
        P.faceArea i * |⟪u, P.normal i⟫| := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hni
    have hn : ¬ ((P.face i).Nonempty ∧
        Module.finrank ℝ (vectorSpan ℝ (P.face i)) = d - 1) :=
      fun hf => hni (Finset.mem_filter.mpr ⟨hi, hf⟩)
    rw [P.faceArea_zero_of_not_facet i hn, zero_mul]
  rw [P.brightness_eq_sum, hsum]
  simp_rw [real_inner_comm u]
  ring

theorem projectionBody_eq_facet_sum :
    projectionBody P.body =
      ∑ i ∈ Finset.univ.filter (fun i => (P.face i).Nonempty ∧
        Module.finrank ℝ (vectorSpan ℝ (P.face i)) = d - 1),
        segment ℝ (-(P.faceArea i / 2) • P.normal i) ((P.faceArea i / 2) • P.normal i) := by
  rw [P.projectionBody_eq_facetZonotope]
  unfold facetZonotope
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i hi hni
  have hn : ¬ ((P.face i).Nonempty ∧
      Module.finrank ℝ (vectorSpan ℝ (P.face i)) = d - 1) :=
    fun hf => hni (Finset.mem_filter.mpr ⟨hi, hf⟩)
  simp only [P.faceArea_zero_of_not_facet i hn, zero_div, neg_zero, zero_smul,
    segment_same, Set.singleton_zero]

end Paper092.HPolytope

end

end OAI
