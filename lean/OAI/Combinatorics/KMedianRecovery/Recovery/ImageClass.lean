import Mathlib

namespace OAI

namespace MetricKMedianRecovery.LocalSearch

variable {B U : Type*} [Fintype B] [Fintype U]

lemma slot_allocation (psi : B → U) (hcard : Fintype.card B ≤ Fintype.card U) :
    ∃ slot : B ↪ U, ∀ b, ∃ c, psi c = psi b ∧ slot c = psi b := by
  classical
  let C : Finset U := Finset.univ.image psi
  have hchoose (u : C) : ∃ b : B, psi b = u.val := by
    obtain ⟨b,_,hb⟩ := Finset.mem_image.mp u.property
    exact ⟨b,hb⟩
  let rep : C → B := fun u => Classical.choose (hchoose u)
  have hrep (u : C) : psi (rep u) = u.val := Classical.choose_spec (hchoose u)
  let R : Finset B := Finset.univ.image rep
  have hinj : Set.InjOn psi R := by
    intro b hb c hc hbc
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hc
    have huv : u = v := Subtype.ext (by simpa only [hrep] using hbc)
    exact congrArg rep huv
  have hC : C.card ≤ Fintype.card B := (Finset.card_image_le).trans (by simp)
  obtain ⟨T,hCT,hTU,hT⟩ := Finset.exists_subsuperset_card_eq
    (s := C) (t := Finset.univ) (Finset.subset_univ _) hC (by simpa using hcard)
  have hRT : R.image psi ⊆ T := by
    intro u hu
    exact hCT (Finset.mem_image.mp hu |>.elim (fun b h =>
      Finset.mem_image.mpr ⟨b,Finset.mem_univ b,h.2⟩))
  obtain ⟨e,he⟩ := Finset.exists_equiv_extend_of_card_eq hT.symm hRT hinj
  refine ⟨e.toEmbedding.trans (Function.Embedding.subtype _),?_⟩
  intro b
  let u : C := ⟨psi b,Finset.mem_image.mpr ⟨b,Finset.mem_univ b,rfl⟩⟩
  refine ⟨rep u,hrep u,?_⟩
  change (e (rep u)).val = psi b
  rw [he _ (Finset.mem_image.mpr ⟨u,Finset.mem_univ u,rfl⟩),hrep]

omit [Fintype B] [Fintype U] in

lemma slot_class_preservation (psi : B → U) (slot : B ↪ U)
    (hslot : ∀ b, ∃ c, psi c = psi b ∧ slot c = psi b)
    {b c : B} (h : slot b = psi c) : psi b = psi c := by
  obtain ⟨d,hd,hds⟩ := hslot c
  have hbd : b = d := slot.injective (h.trans hds.symm)
  simpa [hbd] using hd

noncomputable def imageClass [DecidableEq U] (psi : B → U) (u : U) : Finset B :=
  Finset.univ.filter (fun b => psi b = u)

omit [Fintype U] in
lemma slot_class_card [DecidableEq B] [DecidableEq U] (psi : B → U)
    (slot : B ↪ U) (u : U) :
    ((imageClass psi u).map slot).card = (imageClass psi u).card := by simp

omit [Fintype U] in
lemma image_mem_class_slots [DecidableEq B] [DecidableEq U] (psi : B → U)
    (slot : B ↪ U) (hslot : ∀ b, ∃ c, psi c = psi b ∧ slot c = psi b) (b : B) :
    psi b ∈ (imageClass psi (psi b)).map slot := by
  obtain ⟨c,hc,hs⟩ := hslot b
  exact Finset.mem_map.mpr ⟨c,by simp [imageClass,hc],hs⟩

omit [Fintype U] in
lemma class_slots_disjoint [DecidableEq B] [DecidableEq U] (psi : B → U)
    (slot : B ↪ U) {u v : U} (huv : u ≠ v) :
    Disjoint ((imageClass psi u).map slot) ((imageClass psi v).map slot) := by
  apply Finset.disjoint_left.mpr
  intro s hs ht
  obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hs
  obtain ⟨c,hc,he⟩ := Finset.mem_map.mp ht
  have hcb : c = b := slot.injective he
  have hb' : psi b = u := (Finset.mem_filter.mp hb).2
  have hc' : psi c = v := (Finset.mem_filter.mp hc).2
  exact huv (hb'.symm.trans (hcb ▸ hc'))

end MetricKMedianRecovery.LocalSearch

end OAI
