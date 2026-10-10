import Mathlib
import OAI.Geometry.HyperbolicGroups.WalkClasses
import OAI.Geometry.HyperbolicGroups.RelativeDegree
import OAI.Geometry.HyperbolicGroups.RelativePartitionEstimate
import OAI.Geometry.HyperbolicGroups.PlanarFacePartition

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The random-data-independent cutoff for literal small interior fragments.
The genus-zero planar partition producer is proved, not a hypothesis. -/
theorem uniform_small_interior_partition (eta : ℝ) (heta : 0 < eta) :
    ∃ K : ℕ, 0 < K ∧
    ∀ (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
      (d : (Fin 6 → Alphabet n) → Bool) (ell : ℕ) (hell : 0 < ell)
      (word : Fin ell → Alphabet n)
      (c : Top n w → MacroGraph.graph.Dart → ℤ)
      (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → ℤ)
      (P : WalkPicture.{0} (target n w d ell hell word c hc f)),
      P.Simple → P.NoBigon → P.FrozenMapped (frozen n w d ell hell word c hc f) →
      ∃ (I : Type) (_ : Fintype I) (part : P.Face → I),
        (∀ i, Fintype.card {F : InteriorFace n w d ell hell word c hc f P // part F.val = i} ≤ K) ∧
        (Fintype.card (RelativeCutContact P.pairing
          (Interior n w d ell hell word c hc f P ∘ P.faceClass) (part ∘ P.faceClass)) : ℝ) ≤
          eta * Fintype.card (InteriorFace n w d ell hell word c hc f P) := by
  obtain ⟨K,hK,hh⟩ := uniform_genusZero_face_partition.{0} 15 eta heta
  refine ⟨K,hK,?_⟩
  intro n w d ell hell word c hc f P hs hb hm
  let U : Finset P.Face := Finset.univ.filter (Interior n w d ell hell word c hc f P)
  have hUm (F : P.Face) : F ∈ U ↔ Interior n w d ell hell word c hc f P F := by simp [U]
  have hd (F : P.Face) (hF : F ∈ U) :
      Nat.card {x : P.Dart // P.faceClass x = F} ≤ 15 := by
    have hi : ¬ (walkTarget n w d c hc f).isExterior ell hell (letterDart n w ∘ word)
        (letterWordClosed n w ell word) (P.index F.out) := by
      apply (interior_iff n w d ell hell word c hc f P F.out).mp
      rw [P.faceClass_out]
      exact (hUm F).mp hF
    have he : {x : P.Dart // P.faceClass x = F} ≃
        {x : P.Dart // P.pairing.face.SameCycle F.out x} :=
      Equiv.subtypeEquivRight (fun x => by
        rw [← P.faceClass_eq]
        exact ⟨fun h => (P.faceClass_out F).trans h.symm,
          fun h => h.symm.trans (P.faceClass_out F)⟩)
    rw [Nat.card_congr he,Nat.card_eq_fintype_card]
    exact exterior_interior_degree n w d ell hell (letterDart n w ∘ word)
      (letterWordClosed n w ell word) c hc f P hs hb hm F.out hi
  obtain ⟨I,inst,part,hsize,hcut⟩ := hh P.Dart P.pairing P.genusZero U hd
  let := inst
  have hcard : U.card = Fintype.card (InteriorFace n w d ell hell word c hc f P) := by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight hUm)
  refine ⟨I,inst,part,?_,?_⟩
  · intro i
    have e : {F : InteriorFace n w d ell hell word c hc f P // part F.val = i} ≃
        {F // F ∈ U.filter (fun x => part x = i)} := {
      toFun := fun F => ⟨F.val.val,Finset.mem_filter.mpr ⟨(hUm _).mpr F.val.property,F.property⟩⟩
      invFun := fun F => ⟨⟨F.val,(hUm _).mp (Finset.mem_filter.mp F.property).1⟩,
        (Finset.mem_filter.mp F.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    rw [Fintype.card_congr e,Fintype.card_coe]
    exact hsize i
  · rw [hcard] at hcut
    simp only [← Nat.card_eq_fintype_card] at hcut ⊢
    simpa only [hUm,Function.comp_apply,WalkPicture.faceClass,RelativeCutContact] using hcut

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
