import OAI.Analysis.CircleDomains.Selection.ConcatenatedTags
import OAI.Analysis.CircleDomains.Modulus.TimeIncidenceReparametrization

namespace OAI

/-! Exact old-parameter descriptions of the residual times in each open
piece of a concatenated path, including a clipped global test interval. -/

open Set Function
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem timeIncidence_congr_path {T X Z : Type*} (R : Set (Z × X))
    {γ η : T → X} {A : Set T} (h : EqOn γ η A) :
    timeIncidence R γ A = timeIncidence R η A := by
  ext z
  constructor
  · rintro ⟨t, ht, hr⟩
    exact ⟨t, ht, (h ht) ▸ hr⟩
  · rintro ⟨t, ht, hr⟩
    exact ⟨t, ht, (h ht).symm ▸ hr⟩

theorem timeToll_congr_path {T X : Type*} (m : X → ℝ≥0∞)
    {γ η : T → X} {A : Set T} (h : EqOn γ η A) :
    timeToll γ A m = timeToll η A m := by
  exact tsum_congr fun t => congrArg m (h t.property)

variable {ι X : Type*} [Encodable ι] [MetricSpace X]

theorem concatenated_piece_times (B : Set X)
    (γ : C(PathTime, X)) (a b : ι → PathTime) (hab : ∀ i, a i < b i)
    (hdis : Pairwise (Disjoint on (fun i => Ioo (a i) (b i))))
    (Γ : ι → TaggedPath X)
    (hmatch : ∀ i t, t ∈ Ioo (⊥ : PathTime) ⊤ →
      γ (affinePathTime (a i) (b i) t) = (Γ i).1 t)
    (i : ι) (c d : PathTime) :
    residualTimes B (concatenatedTaggedPath γ a b Γ) ∩ (Ioo (a i) (b i) ∩ Ioo c d) =
      affinePathTime (a i) (b i) '' (residualTimes B (Γ i) ∩
        Ioo (rescalePathTime (a i) (b i) c) (rescalePathTime (a i) (b i) d)) := by
  ext t
  constructor
  · rintro ⟨hr, hj, ht⟩
    have himage : t ∈ affinePathTime (a i) (b i) ''
        Ioo (rescalePathTime (a i) (b i) c) (rescalePathTime (a i) (b i) d) := by
      rw [affine_image_rescaled_Ioo (hab i)]
      exact ⟨hj, ht⟩
    obtain ⟨s, hs, he⟩ := himage
    refine ⟨s, ⟨?_, hs⟩, he⟩
    have hold := (residualTimes_concatenated_piece B γ a b hab hdis Γ hmatch i hj).mp hr
    rwa [← he, rescale_affinePathTime (hab i)] at hold
  · rintro ⟨s, ⟨hr, hs⟩, rfl⟩
    have hpiece : affinePathTime (a i) (b i) s ∈ Ioo (a i) (b i) ∩ Ioo c d := by
      rw [← affine_image_rescaled_Ioo (hab i)]
      exact ⟨s, hs, rfl⟩
    refine ⟨?_, hpiece⟩
    apply (residualTimes_concatenated_piece B γ a b hab hdis Γ hmatch i hpiece.1).mpr
    rwa [rescale_affinePathTime (hab i)]

end CircleDomainRigidity

end

end OAI
