import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeFullNormal
import OAI.Geometry.HyperbolicGroups.WalkClasses
import OAI.Geometry.HyperbolicGroups.ActualDegree
import OAI.Geometry.HyperbolicGroups.PlanarFacePartition

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
open Occurrences.Shape
attribute [local instance] Classical.propDecidable
universe u v

/-- Unbounded normal spherical-picture vanishing. The size cutoff is in the
rank EVENT, not in the picture: the theorem applies to every finite normal
picture for that realization, without any assumed separator interface. -/
theorem uniform_normal_picture_empty {α β δ : ℝ}
    (ha : 0 < α) (hb : 7*α < β) (hd : 0 < δ) :
    ∃ K : ℕ, 0 < K ∧ ∀ (n : ℕ)
      (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
      (d : (Fin 6 → Alphabet n) → Bool),
      Occurrences.GoodUpTo (8*K) α β δ (Sum.elim w d) →
      ∀ (A : Type v) [AddCommGroup A]
        (c : Top n w → MacroGraph.graph.Dart → A)
        (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
        (P : WalkPicture.{u} (walkTarget n w d c hc f)),
        P.Simple → P.FrozenMapped (walkFrozenTarget n w d c hc f) →
        P.FullyReduced → P.RadialInjective (isApex n w) → P.NoBigon → IsEmpty P.Dart := by
  have hk := defectConstant_pos ha hb hd
  obtain ⟨K,hK,hh⟩ := uniform_genusZero_face_partition.{u} 15
    (defectConstant α β δ / 4) (div_pos hk (by norm_num))
  refine ⟨K,hK,?_⟩
  intro n w d hgood A _ c hc f P hs hm hred hrad hbig
  let U : Finset P.Face := Finset.univ
  have hdegree (F : P.Face) (_ : F ∈ U) :
      Nat.card {x : P.Dart // P.faceClass x = F} ≤ 15 := by
    rw [Nat.card_eq_fintype_card]
    exact actual_face_degree_le n w d c hc f P hs hbig hm F
  obtain ⟨I,inst,part,hsize,hcut⟩ := hh P.Dart P.pairing P.genusZero U hdegree
  let := inst
  apply normal_empty_of_sparse_partition n w d c hc f P part ha hb hd
    (η := defectConstant α β δ / 4) (by linarith) hgood hs hm hred hrad hbig
  · intro i
    simpa only [U,← Fintype.card_subtype] using hsize i
  · simp only [← Nat.card_eq_fintype_card] at hcut ⊢
    simpa only [U,Finset.mem_univ,Finset.card_univ,RelativeCutContact,CutContact,
      true_and,WalkPicture.faceClass,Function.comp_apply,← Nat.card_eq_fintype_card] using hcut

/-- Every literal genus-zero closed picture carries zero chain, after the
proved finite normal-form surgeries. This is not yet the topological theorem
that a nonzero Hurewicz cycle admits such a picture. -/
theorem uniform_closed_picture_chain_zero {α β δ : ℝ}
    (ha : 0 < α) (hb : 7*α < β) (hd : 0 < δ) :
    ∃ M : ℕ, 0 < M ∧ ∀ (n : ℕ)
      (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
      (d : (Fin 6 → Alphabet n) → Bool),
      Occurrences.GoodUpTo M α β δ (Sum.elim w d) →
      ∀ (A : Type v) [AddCommGroup A]
        (c : Top n w → MacroGraph.graph.Dart → A)
        (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
        (P : WalkPicture.{u} (walkTarget n w d c hc f)),
        P.FrozenMapped (walkFrozenTarget n w d c hc f) → P.chain = 0 := by
  obtain ⟨K,hK,hh⟩ := uniform_normal_picture_empty.{u,v} ha hb hd
  refine ⟨8*K,Nat.mul_pos (by decide) hK,?_⟩
  intro n w d hgood A _ c hc f P hm
  obtain ⟨Q,_,hmQ,hsQ,hbQ,hrQ,hradQ,hchain,_⟩ := normalizedPicture n w d c hc f P hm
  have : IsEmpty Q.Dart := hh n w d hgood A c hc f Q hsQ hmQ hrQ hradQ hbQ
  rw [← hchain]
  simp only [WalkPicture.chain,Finset.univ_eq_empty,Finset.sum_empty]

end HyperbolicObstruction.ConeSkeleton
end

end OAI
