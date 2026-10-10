import Mathlib.Combinatorics.SetFamily.HarrisKleitman
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith

namespace OAI

namespace PlanarFPP
open Finset
variable {α : Type*} [DecidableEq α]

def UpwardFamily (s : Finset α) (A : Finset (Finset α)) : Prop :=
  (∀ x ∈ A, x ⊆ s) ∧ ∀ x ∈ A, ∀ y, x ⊆ y → y ⊆ s → y ∈ A

noncomputable def disjointOccurrenceFamily (s : Finset α) (A B : Finset (Finset α)) : Finset (Finset α) :=
  by
    classical
    exact s.powerset.filter (fun x => ∃ a ∈ A, ∃ b ∈ B, a ⊆ x ∧ b ⊆ x ∧ Disjoint a b)

lemma mem_disjointOccurrenceFamily (s : Finset α) (A B : Finset (Finset α)) (x : Finset α) :
    x ∈ disjointOccurrenceFamily s A B ↔
      x ⊆ s ∧ ∃ a ∈ A, ∃ b ∈ B, a ⊆ x ∧ b ⊆ x ∧ Disjoint a b := by
  classical
  simp [disjointOccurrenceFamily]

lemma disjointOccurrenceFamily_mono (s : Finset α) {A A' B B' : Finset (Finset α)}
    (hA : A ⊆ A') (hB : B ⊆ B') :
    disjointOccurrenceFamily s A B ⊆ disjointOccurrenceFamily s A' B' := by
  intro x hx
  obtain ⟨hs,a,ha,b,hb,hax,hbx,hab⟩ := (mem_disjointOccurrenceFamily ..).mp hx
  exact (mem_disjointOccurrenceFamily ..).mpr ⟨hs,a,hA ha,b,hB hb,hax,hbx,hab⟩

lemma UpwardFamily.nonMember {s : Finset α} {A : Finset (Finset α)} {e : α}
    (he : e ∉ s) (hA : UpwardFamily (insert e s) A) :
    UpwardFamily s (A.nonMemberSubfamily e) := by
  constructor
  · intro x hx
    obtain ⟨hx,he'⟩ := mem_nonMemberSubfamily.mp hx
    exact (subset_insert_iff_of_notMem he').mp (hA.1 x hx)
  · intro x hx y hxy hys
    obtain ⟨hx,hex⟩ := mem_nonMemberSubfamily.mp hx
    exact mem_nonMemberSubfamily.mpr ⟨hA.2 x hx y hxy (hys.trans (subset_insert _ _)),
      fun hey => he (hys hey)⟩

lemma UpwardFamily.member {s : Finset α} {A : Finset (Finset α)} {e : α}
    (he : e ∉ s) (hA : UpwardFamily (insert e s) A) :
    UpwardFamily s (A.memberSubfamily e) := by
  constructor
  · intro x hx
    obtain ⟨hx,hex⟩ := mem_memberSubfamily.mp hx
    exact (subset_insert_iff_of_notMem hex).mp ((subset_insert _ _).trans (hA.1 _ hx))
  · intro x hx y hxy hys
    obtain ⟨hx,hex⟩ := mem_memberSubfamily.mp hx
    exact mem_memberSubfamily.mpr ⟨hA.2 _ hx _ (insert_subset_insert _ hxy)
      (insert_subset_insert _ hys),fun hey => he (hys hey)⟩

lemma UpwardFamily.slice_subset {s : Finset α} {A : Finset (Finset α)} {e : α}
    (hA : UpwardFamily (insert e s) A) : A.nonMemberSubfamily e ⊆ A.memberSubfamily e := by
  intro x hx
  obtain ⟨hx,hex⟩ := mem_nonMemberSubfamily.mp hx
  exact mem_memberSubfamily.mpr ⟨hA.2 x hx _ (subset_insert _ _)
    (by intro y hy; rcases mem_insert.mp hy with rfl | hy; exact mem_insert_self _ _; exact hA.1 x hx hy),hex⟩

lemma disjointOccurrence_nonMember (s : Finset α) (A B : Finset (Finset α)) (e : α) (he : e ∉ s) :
    (disjointOccurrenceFamily (insert e s) A B).nonMemberSubfamily e =
      disjointOccurrenceFamily s (A.nonMemberSubfamily e) (B.nonMemberSubfamily e) := by
  ext x
  simp only [mem_nonMemberSubfamily,mem_disjointOccurrenceFamily]
  constructor
  · rintro ⟨⟨hxs,a,ha,b,hb,hax,hbx,hab⟩,hex⟩
    exact ⟨(subset_insert_iff_of_notMem hex).mp hxs,a,⟨ha,fun he => hex (hax he)⟩,
      b,⟨hb,fun he => hex (hbx he)⟩,hax,hbx,hab⟩
  · rintro ⟨hxs,a,⟨ha,hea⟩,b,⟨hb,heb⟩,hax,hbx,hab⟩
    refine ⟨⟨hxs.trans (subset_insert _ _),a,ha,b,hb,hax,hbx,hab⟩,?_⟩
    exact fun hex => he (hxs hex)

lemma erase_subset_of_subset_insert {e : α} {a x : Finset α} (ha : a ⊆ insert e x) :
    a.erase e ⊆ x := by
  intro v hv
  obtain ⟨hne,hva⟩ := mem_erase.mp hv
  exact (mem_insert.mp (ha hva)).resolve_left hne

lemma disjointOccurrence_member (s : Finset α) (A B : Finset (Finset α)) (e : α)
    (he : e ∉ s) (hA : UpwardFamily (insert e s) A) (hB : UpwardFamily (insert e s) B) :
    (disjointOccurrenceFamily (insert e s) A B).memberSubfamily e =
      disjointOccurrenceFamily s (A.memberSubfamily e) (B.nonMemberSubfamily e) ∪
      disjointOccurrenceFamily s (A.nonMemberSubfamily e) (B.memberSubfamily e) := by
  ext x
  simp only [mem_memberSubfamily,mem_union,mem_disjointOccurrenceFamily]
  constructor
  · rintro ⟨⟨hxs,a,ha,b,hb,hax,hbx,hab⟩,hex⟩
    have hxs' : x ⊆ s := (subset_insert_iff_of_notMem hex).mp ((subset_insert _ _).trans hxs)
    by_cases hea : e ∈ a
    · have heb : e ∉ b := fun hb' => Finset.disjoint_left.mp hab hea hb'
      left
      refine ⟨hxs',a.erase e,?_,b,mem_nonMemberSubfamily.mpr ⟨hb,heb⟩,erase_subset_of_subset_insert hax,?_,?_⟩
      · exact ⟨by simpa [insert_erase hea] using ha,notMem_erase _ _⟩
      · exact (subset_insert_iff_of_notMem heb).mp hbx
      · exact hab.mono_left (erase_subset _ _)
    · right
      refine ⟨hxs',a,mem_nonMemberSubfamily.mpr ⟨ha,hea⟩,b.erase e,?_,
        (subset_insert_iff_of_notMem hea).mp hax,erase_subset_of_subset_insert hbx,?_⟩
      · refine ⟨hB.2 b hb _ (by intro v hv; by_cases heq : v=e; exact mem_insert.mpr (Or.inl heq); exact mem_insert.mpr (Or.inr (mem_erase.mpr ⟨heq,hv⟩))) ?_,notMem_erase _ _⟩
        intro v hv
        rcases mem_insert.mp hv with rfl | hv
        · exact mem_insert_self _ _
        · exact hB.1 b hb (mem_of_mem_erase hv)
      · exact hab.mono_right (erase_subset _ _)
  · intro hx
    rcases hx with ⟨hxs,a,⟨ha,hea⟩,b,hb,hax,hbx,hab⟩ | ⟨hxs,a,ha,b,⟨hb,heb⟩,hax,hbx,hab⟩
    · obtain ⟨hb,heb⟩ := mem_nonMemberSubfamily.mp hb
      refine ⟨⟨insert_subset_insert _ hxs,insert e a,ha,b,hb,
        insert_subset_insert _ hax,hbx.trans (subset_insert _ _),?_⟩,fun h => he (hxs h)⟩
      exact Finset.disjoint_insert_left.mpr ⟨heb,hab⟩
    · obtain ⟨ha,hea⟩ := mem_nonMemberSubfamily.mp ha
      refine ⟨⟨insert_subset_insert _ hxs,a,ha,insert e b,hb,
        hax.trans (subset_insert _ _),insert_subset_insert _ hbx,?_⟩,fun h => he (hxs h)⟩
      exact Finset.disjoint_insert_right.mpr ⟨hea,hab⟩

theorem finite_fair_BK (s : Finset α) (A B : Finset (Finset α))
    (hA : UpwardFamily s A) (hB : UpwardFamily s B) :
    2^s.card*(disjointOccurrenceFamily s A B).card ≤ A.card*B.card := by
  classical
  induction s using Finset.induction_on generalizing A B with
  | empty =>
    have hAs := hA.1
    have hBs := hB.1
    simp_rw [subset_empty,← subset_singleton_iff',subset_singleton_iff] at hAs hBs
    rcases hAs with rfl | rfl <;> rcases hBs with rfl | rfl <;>
      simp [disjointOccurrenceFamily]
  | @insert e s he ih =>
    let D₀ := disjointOccurrenceFamily s (A.nonMemberSubfamily e) (B.nonMemberSubfamily e)
    let D₁ := disjointOccurrenceFamily s (A.memberSubfamily e) (B.nonMemberSubfamily e)
    let D₂ := disjointOccurrenceFamily s (A.nonMemberSubfamily e) (B.memberSubfamily e)
    have h₀₁ : D₀ ⊆ D₁ := disjointOccurrenceFamily_mono s hA.slice_subset (Subset.rfl)
    have h₀₂ : D₀ ⊆ D₂ := disjointOccurrenceFamily_mono s (Subset.rfl) hB.slice_subset
    have hcount : (disjointOccurrenceFamily (insert e s) A B).card ≤ D₁.card+D₂.card := by
      rw [← card_memberSubfamily_add_card_nonMemberSubfamily e,
        disjointOccurrence_member s A B e he hA hB,disjointOccurrence_nonMember s A B e he]
      have hh := Finset.card_le_card (subset_inter h₀₁ h₀₂)
      have hu := Finset.card_union_add_card_inter D₁ D₂
      change (D₁ ∪ D₂).card+D₀.card ≤ D₁.card+D₂.card
      omega
    have h₁ := ih _ _ (hA.member he) (hB.nonMember he)
    have h₂ := ih _ _ (hA.nonMember he) (hB.member he)
    have hca := Finset.card_le_card hA.slice_subset
    have hcb := Finset.card_le_card hB.slice_subset
    have hcross := mul_add_mul_le_mul_add_mul hca hcb
    have ha := card_memberSubfamily_add_card_nonMemberSubfamily e A
    have hb := card_memberSubfamily_add_card_nonMemberSubfamily e B
    have hmul := Nat.mul_le_mul_left (2^s.card) hcount
    rw [Finset.card_insert_of_notMem he,pow_succ]
    dsimp [D₁,D₂] at hmul
    nlinarith

end PlanarFPP

end OAI
