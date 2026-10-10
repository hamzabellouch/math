import OAI.NumberTheory.DukePrimeDegree.Dynamics.PublishedEKL

namespace OAI

/-!
# Translation covariance of root boxes

A measure-preserving root translation transports the actual coordinate
measure and its disintegration. This is the local input for identifying
invariant root conditionals with Lebesgue measure.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace DukePrimeDegree
open PrimeDegreePackets
open PrimeDegreePackets.RootBox
namespace RootBox

variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

def translate (B : PrimeDegreePackets.RootBox hij k) (a : ℝ) :
    PrimeDegreePackets.RootBox hij k := by
  let E := timeTranslation (i := i) (j := j) (k := k) a
  let f := Homeomorph.addRight a
  have hiff (z : RootSlice i j k × ℝ) :
      z ∈ B.domain ↔ E z ∈ B.transverse ×ˢ (f '' B.time) := by
    change (z.1 ∈ B.transverse ∧ z.2 ∈ B.time) ↔
      (z.1 ∈ B.transverse ∧ f z.2 ∈ f '' B.time)
    rw [f.injective.mem_set_image]
  let eb := E.subtype hiff
  refine ⟨B.transverse, f '' B.time, B.transverse_open,
    f.isOpenMap _ B.time_open, ?_⟩
  have H := (rightActionHomeomorph (Matrix.SpecialLinearGroup.transvection hij a)).isOpenEmbedding.comp
    (B.embedding.comp eb.symm.isOpenEmbedding)
  convert H using 1
  funext z
  have he : E (eb.symm z).val = z.val := congrArg Subtype.val (eb.apply_symm_apply z)
  change rootQuotientParametrization hij z.val =
    rightAction (rootQuotientParametrization hij (eb.symm z).val)
      (Matrix.SpecialLinearGroup.transvection hij a)
  rw [← he]
  exact rootQuotientParametrization_add hij _ _ _

lemma translate_domain (B : PrimeDegreePackets.RootBox hij k) (a : ℝ) :
    (translate B a).domain = timeTranslation a '' B.domain := by
  ext z
  constructor
  · rintro ⟨hs, t, ht, he⟩
    exact ⟨(z.1, t), ⟨hs, ht⟩, Prod.ext rfl he⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hz.1, z.2, hz.2, rfl⟩

theorem translate_coordinateMeasure (B : PrimeDegreePackets.RootBox hij k)
    (a : ℝ) (μ : Measure (X n))
    (hinv : μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = μ) :
    (translate B a).coordinateMeasure μ = (B.coordinateMeasure μ).map (timeTranslation a) := by
  let E := timeTranslation (i := i) (j := j) (k := k) a
  let H := rightActionHomeomorph (Matrix.SpecialLinearGroup.transvection hij a)
  have hμ (S : Set (X n)) : μ (H '' S) = μ S := by
    calc
      μ (H '' S) = (μ.map H) (H '' S) := congrArg (fun ν => ν (H '' S)) hinv.symm
      _ = μ S := by
        rw [H.isOpenEmbedding.measurableEmbedding.map_apply, H.injective.preimage_image]
  ext S hS
  rw [Measure.map_apply E.continuous.measurable hS,
    PrimeDegreePackets.RootBox.coordinateMeasure_apply _ μ hS,
    PrimeDegreePackets.RootBox.coordinateMeasure_apply _ μ (E.continuous.measurable hS),
    translate_domain]
  rw [← hμ (rootQuotientParametrization hij '' (E ⁻¹' S ∩ B.domain))]
  congr 1
  ext x
  constructor
  · rintro ⟨z, ⟨hzS, w, hw, rfl⟩, rfl⟩
    exact ⟨rootQuotientParametrization hij w, ⟨w, ⟨hzS, hw⟩, rfl⟩,
      (rootQuotientParametrization_add hij w.1 w.2 a).symm⟩
  · rintro ⟨_, ⟨w, ⟨hwS, hw⟩, rfl⟩, rfl⟩
    exact ⟨E w, ⟨hwS, ⟨w, hw, rfl⟩⟩, rootQuotientParametrization_add hij w.1 w.2 a⟩

theorem translate_marginal (B : PrimeDegreePackets.RootBox hij k)
    (a : ℝ) (μ : Measure (X n))
    (hinv : μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = μ) :
    ((translate B a).coordinateMeasure μ).fst = (B.coordinateMeasure μ).fst := by
  rw [translate_coordinateMeasure B a μ hinv]
  have h := fst_map_measurableEquiv (B.coordinateMeasure μ)
    (MeasurableEquiv.refl (RootSlice i j k)) (Homeomorph.addRight a).toMeasurableEquiv
  change ((B.coordinateMeasure μ).map (timeTranslation a)).fst =
    ((B.coordinateMeasure μ).fst).map id at h
  simpa only [Measure.map_id] using h

theorem translate_conditionalKernel (B : PrimeDegreePackets.RootBox hij k)
    (a : ℝ) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hinv : μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = μ) :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst,
      (translate B a).conditionalKernel μ s =
        (B.conditionalKernel μ s).map (Homeomorph.addRight a) := by
  simp only [PrimeDegreePackets.RootBox.conditionalKernel, translate_coordinateMeasure B a μ hinv]
  exact condKernel_map_measurableEquiv (B.coordinateMeasure μ)
    (MeasurableEquiv.refl (RootSlice i j k)) (Homeomorph.addRight a).toMeasurableEquiv

end RootBox
end DukePrimeDegree

end

end OAI
