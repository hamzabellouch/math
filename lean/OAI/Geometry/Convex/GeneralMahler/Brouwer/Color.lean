import OAI.Geometry.Convex.GeneralMahler.Brouwer.Ghost

namespace OAI
/-! Incidence parity implies a full room for every coloring. -/
noncomputable section
open Finset
namespace GeneralMahler.Scarf
variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [Nonempty T]

omit [DecidableEq I] [Fintype T] [Nonempty T] in
lemma erase_door {r : Orders I T} {s} (hs:room r s) {x:T} (hx:x∈s) :
    door r (s.erase x) := by
  have hpos : 0<s.card := Finset.card_pos.mpr ⟨_,hx⟩
  refine ⟨?_,dom_subset r (erase_subset ..) hs.2⟩
  rw [card_erase_of_mem hx,← hs.1]; omega

omit [Fintype T] [Nonempty T] in
lemma two_if_not_colorful (r : Orders I T) (c:T→I) (i:I) {s:Finset T}
    (h : room r s) (hn : s.image c ≠ univ)
    (p : Finset T → Prop)
    (hp : ∀ d, p d ↔ door r d ∧ d⊆s ∧ d.image c=univ.erase i)
    (he : ∃ d,p d) :
    ∃ x y, x≠y ∧ ∀ d, p d ↔ d=x ∨ d=y := by
  obtain ⟨d₀,hd₀⟩ := he
  obtain ⟨ht,hds,heq⟩ := (hp d₀).mp hd₀
  have hh : s.image c=univ.erase i := Finset.Subset.antisymm (fun x hx=>by
    have hskip : x≠i := by
      intro a; subst x
      apply hn
      ext x
      simp only [mem_univ, iff_true]
      by_cases hv:x=i
      · subst x; exact hx
      · exact Finset.image_subset_image hds (by simp [heq,hv])
    simpa using hskip) (heq ▸ Finset.image_subset_image hds)
  have hI : Fintype.card I > 0 := Fintype.card_pos_iff.mpr ⟨i⟩
  obtain ⟨x,hx,y,hy,hxy,hf,he⟩ := duplicate_pair (s := s) c (by
    rw [h.1,hh, Finset.card_erase_of_mem (mem_univ i), card_univ]
    omega)
  refine ⟨s.erase x,s.erase y,?_,fun d=>?_⟩
  · intro h
    have hn : y ∈ s.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy,hy⟩
    rw [h] at hn
    simp at hn
  constructor
  · intro h₁
    obtain ⟨h₂,h₃,h₄⟩ := (hp d).mp h₁
    obtain ⟨z,hz,heq⟩ := Finset.exists_eq_insert_iff.mpr
      ⟨h₃,h₂.1.symm.trans h.1.symm⟩
    have hzs : z∈s := heq ▸ mem_insert_self ..
    have hm : d=s.erase z := by simp [← heq,hz]
    have hn : c z ∈ d.image c :=
      (hh.trans h₄.symm) ▸ Finset.mem_image_of_mem _ hzs
    obtain ⟨l,hl,hl'⟩ := Finset.mem_image.mp hn
    have hn : z≠l := by rintro hh; subst l; exact hz hl
    rcases he z hzs l (h₃ hl) hn hl'.symm with ⟨he,-⟩|⟨he,-⟩ <;> simp [hm,he]
  · rintro (rfl|rfl)
    · exact (hp _).mpr ⟨erase_door h hx, Finset.erase_subset .., (image_erase_eq' hy hxy hf).trans hh⟩
    · exact (hp _).mpr ⟨erase_door h hy, Finset.erase_subset ..,
        (image_erase_eq' hx (Ne.symm hxy) hf.symm).trans hh⟩

lemma count_unique [Fintype X] {p : X → Prop} [DecidablePred p]
    (h : ∃! x,p x) :
    ∑ x:X, (if p x then (1:ZMod 2) else 0) = 1 := by
  classical
  obtain ⟨x,hx,he⟩ := h
  rw [sum_eq_single x] <;> grind

lemma count_two [Fintype X] {p : X → Prop} [DecidablePred p]
    (h : ∃ x y, x≠y ∧ ∀ i, p i ↔ i=x ∨ i=y) :
    ∑ x:X, (if p x then (1:ZMod 2) else 0) = 0 := by
  classical
  obtain ⟨x,y,hx,he⟩ := h
  rw [← Finset.add_sum_erase univ _ (mem_univ x),
    Finset.sum_eq_single y]
  · simp [he]; decide
  · intro i hi h
    have hu : i≠x := (Finset.mem_erase.mp hi).1
    simp [he,hu,h]
  simp [Ne.symm hx]

theorem full_room [Nonempty I] (q : GOrders I T) (f : T → I) :
    ∃ s, room q.toOrders s ∧ s.image (Sum.elim id f) = univ := by
  classical
  obtain ⟨i⟩ := ‹Nonempty I›
  let c : I⊕T → I := Sum.elim id f
  let r := q.toOrders
  let P := fun (d s:Finset (I⊕T)) =>
    door r d ∧ room r s ∧ d ⊆ s ∧ d.image c = Finset.univ.erase i
  let H := fun d s => if P d s then (1:ZMod 2) else 0
  by_contra hh
  have hc (s) (hs: room r s) : s.image c ≠ univ := fun h => hh ⟨s,hs,h⟩
  have hr (s) : ∑ d,H d s = 0 := by
    by_cases h:∃ d,P d s
    · apply count_two
      obtain ⟨d,hd⟩ := h
      have hs := hd.2.1
      exact two_if_not_colorful r c i hs (hc _ hs) _ (by simp [P,hs]) ⟨d,hd⟩
    · simp only [not_exists] at h
      simp [H,h]
  let d₀ : Finset (I⊕T) := outer i
  have he : ∑ s,H d₀ s=1 := by
    have h : d₀.image c = univ.erase i := by simp [d₀,outer,image_image,c,Function.comp_def]
    have hh : door r d₀ := outer_door q _
    apply count_unique
    simpa [P,h,hh] using extension_outer q i
  have hm (d:Finset (I⊕T)) (hd:d≠d₀) : ∑ s,H d s=0 := by
    by_cases h:∃ s,P d s
    · obtain ⟨s,hs,Ht,hds,Hc⟩ := h
      have hh : inside d := by
        by_contra hno
        refine hd ?_
        ext x
        cases x with
        | inl j =>
          have hmem : j ∈ d.image c ↔ Sum.inl j ∈ d := by
            constructor
            · intro hv
              obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hv
              cases y with
              | inl y =>
                change y=j at he; subst j; exact hy
              | inr y => exact False.elim (hno ⟨_,hy⟩)
            · intro hy; exact Finset.mem_image.mpr ⟨_,hy,by simp [c]⟩
          rw [← hmem,Hc,mem_outer]; simp
        | inr y =>
          exact iff_of_false (fun hh => hno ⟨y,hh⟩) (not_mem_outer i y)
      apply count_two
      simpa [P,hs,Hc] using extensions_two q hs hh
    · simp only [not_exists] at h
      simp [H,h]
  have hs := Finset.sum_comm (s := univ) (t := univ) (f := H)
  simp_rw [hr,Finset.sum_const_zero] at hs
  rw [Finset.sum_eq_single d₀] at hs
  · rw [he] at hs
    exact one_ne_zero hs
  · exact fun _ _ h=>hm _ h
  simp

end GeneralMahler.Scarf

end

end OAI
