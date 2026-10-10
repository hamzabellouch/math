import OAI.Combinatorics.ListHadwiger.Footprint

namespace OAI

namespace LinearListHadwiger.Footprint
open Finset
attribute [local instance] Classical.propDecidable

structure History {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (t : ℕ) where
  q : ℕ
  footprint : ℕ → Finset V
  initial_card : (footprint 0).card ≤ t
  tips : Fin q → Finset V
  district : Fin q → Finset V
  junction : Fin q → Finset V
  roots : Fin q → Finset V
  first : Fin q → System G
  second : Fin q → System G
  tips_subset : ∀ i, tips i ⊆ footprint i.val
  tips_card : ∀ i, (tips i).card ≤ t
  district_card : ∀ i, ((district i).card:ℝ) ≤ (t:ℝ)^(106/100:ℝ)
  junction_card : ∀ i, ((junction i).card:ℝ) ≤ (t:ℝ)^(106/100:ℝ)
  district_disjoint : ∀ i, Disjoint (district i) (footprint i.val)
  junction_disjoint : ∀ i, Disjoint (junction i) (footprint i.val ∪ district i)
  roots_subset : ∀ i, roots i ⊆ district i
  first_domain : ∀ i, (first i).domain = univ \ (footprint i.val \ tips i)
  first_starts : ∀ i, (first i).starts ⊆ tips i ∪ roots i
  tips_start : ∀ i, tips i ⊆ (first i).starts
  first_ends : ∀ i, (first i).ends ⊆ junction i
  first_count : ∀ i, (first i).n ≤ 4*t
  second_domain : ∀ i, (second i).domain = univ \ (footprint i.val ∪ roots i)
  second_starts : ∀ i, Disjoint (second i).starts
    (footprint i.val ∪ district i ∪ junction i ∪ (first i).used)
  second_injective : ∀ i, Function.Injective (second i).source
  second_ends : ∀ i, (second i).ends ⊆ junction i
  second_count : ∀ i, (second i).n ≤ 2*t
  next : ∀ i, footprint (i.val+1) = footprint i.val ∪ district i ∪ junction i ∪
    (first i).used ∪ (second i).used

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t : ℕ}
namespace History

lemma step_subset (H : History G t) (i : Fin H.q) :
    H.footprint i.val ⊆ H.footprint (i.val+1) := by
  rw [H.next i]
  exact subset_union_left.trans (subset_union_left.trans
    (subset_union_left.trans subset_union_left))

lemma footprint_mono (H : History G t) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ H.q) :
    H.footprint a ⊆ H.footprint b := by
  induction hab with
  | refl => exact Subset.rfl
  | @step b hab ih =>
    exact (ih (by omega)).trans (H.step_subset ⟨b,by omega⟩)

lemma first_used_next (H : History G t) (i : Fin H.q) :
    (H.first i).used ⊆ H.footprint (i.val+1) := by
  rw [H.next i]
  exact subset_union_right.trans subset_union_left

lemma second_used_next (H : History G t) (i : Fin H.q) :
    (H.second i).used ⊆ H.footprint (i.val+1) := by
  rw [H.next i]
  exact subset_union_right

lemma district_next (H : History G t) (i : Fin H.q) :
    H.district i ⊆ H.footprint (i.val+1) := by
  rw [H.next i]
  exact subset_union_right.trans (subset_union_left.trans (subset_union_left.trans subset_union_left))

lemma roots_next (H : History G t) (i : Fin H.q) :
    H.roots i ⊆ H.footprint (i.val+1) := (H.roots_subset i).trans (H.district_next i)

lemma first_stripped_avoids (H : History G t) (i : Fin H.q) (j : Fin (H.first i).n) :
    Disjoint ((H.first i).stripped j) (H.footprint i.val) := by
  apply disjoint_left.mpr
  intro v hv hvF
  have hvp := (mem_sdiff.mp hv).1
  have hvD := (H.first i).path_subset_domain j hvp
  rw [H.first_domain i] at hvD
  have hvt : v ∈ H.tips i := by
    by_contra hnt
    exact (mem_sdiff.mp hvD).2 (mem_sdiff.mpr ⟨hvF,hnt⟩)
  have he := (H.first i).start_on_path j hvp (H.tips_start i hvt)
  exact (mem_sdiff.mp hv).2 (mem_singleton.mpr he)

lemma second_avoids (H : History G t) (i : Fin H.q) :
    Disjoint (H.second i).used (H.footprint i.val) := by
  apply disjoint_left.mpr
  intro v hv hvF
  have hvD := (H.second i).used_subset_domain hv
  rw [H.second_domain i] at hvD
  exact (mem_sdiff.mp hvD).2 (mem_union_left _ hvF)

abbrev FirstIndex (H : History G t) := Σ i : Fin H.q, Fin (H.first i).n
abbrev SecondIndex (H : History G t) := Σ i : Fin H.q, Fin (H.second i).n
noncomputable def firstPath (H : History G t) (i : H.FirstIndex) : Finset V :=
  (H.first i.1).stripped i.2
noncomputable def secondPath (H : History G t) (i : H.SecondIndex) : Finset V :=
  (H.second i.1).path i.2

lemma firstPath_next (H : History G t) (i : H.FirstIndex) :
    H.firstPath i ⊆ H.footprint (i.1.val+1) :=
  sdiff_subset.trans (((H.first i.1).path_subset_used i.2).trans (H.first_used_next i.1))

lemma secondPath_next (H : History G t) (i : H.SecondIndex) :
    H.secondPath i ⊆ H.footprint (i.1.val+1) :=
  ((H.second i.1).path_subset_used i.2).trans (H.second_used_next i.1)

lemma firstPath_connected (H : History G t) (i : H.FirstIndex) :
    (G.induce (↑(H.firstPath i) : Set V)).Connected := by
  apply System.stripped_connected
  intro he
  have hs := H.first_starts i.1 (show ((H.first i.1).source i.2).val ∈ (H.first i.1).starts from
    mem_image.mpr ⟨i.2,mem_univ _,rfl⟩)
  have hs' : ((H.first i.1).source i.2).val ∈ H.footprint i.1.val ∪ H.district i.1 := by
    rcases mem_union.mp hs with hs | hs
    · exact mem_union_left _ (H.tips_subset i.1 hs)
    · exact mem_union_right _ (H.roots_subset i.1 hs)
  have he' := H.first_ends i.1 (show ((H.first i.1).routes.paths i.2).1.val ∈
      (H.first i.1).ends from mem_image.mpr ⟨i.2,mem_univ _,rfl⟩)
  rw [he] at hs'
  exact disjoint_left.mp (H.junction_disjoint i.1) he' hs'

lemma secondPath_connected (H : History G t) (i : H.SecondIndex) :
    (G.induce (↑(H.secondPath i) : Set V)).Connected := (H.second i.1).path_connected i.2

lemma firstPath_disjoint (H : History G t) (i j : H.FirstIndex) (hij : i ≠ j) :
    Disjoint (H.firstPath i) (H.firstPath j) := by
  rcases lt_trichotomy i.1.val j.1.val with hlt | he | hgt
  · apply Disjoint.mono_left ((H.firstPath_next i).trans (H.footprint_mono (b := j.1.val) (by omega) (by omega)))
    exact (H.first_stripped_avoids j.1 j.2).symm
  · obtain ⟨i,a⟩ := i
    obtain ⟨j,b⟩ := j
    have he' : i=j := Fin.ext he
    subst j
    apply System.stripped_disjoint
    intro he
    exact hij (by cases he; rfl)
  · apply Disjoint.mono_right ((H.firstPath_next j).trans (H.footprint_mono (b := i.1.val) (by omega) (by omega)))
    exact H.first_stripped_avoids i.1 i.2

lemma secondPath_disjoint (H : History G t) (i j : H.SecondIndex) (hij : i ≠ j) :
    Disjoint (H.secondPath i) (H.secondPath j) := by
  rcases lt_trichotomy i.1.val j.1.val with hlt | he | hgt
  · apply Disjoint.mono_left ((H.secondPath_next i).trans (H.footprint_mono (b := j.1.val) (by omega) (by omega)))
    exact ((H.second_avoids j.1).mono_left ((H.second j.1).path_subset_used j.2)).symm
  · obtain ⟨i,a⟩ := i
    obtain ⟨j,b⟩ := j
    have he' : i=j := Fin.ext he
    subst j
    apply System.paths_disjoint _ (H.second_injective i)
    intro he
    exact hij (by cases he; rfl)
  · apply Disjoint.mono_right ((H.secondPath_next j).trans (H.footprint_mono (b := i.1.val) (by omega) (by omega)))
    exact (H.second_avoids i.1).mono_left ((H.second i.1).path_subset_used i.2)

lemma firstIndex_card (H : History G t) : Fintype.card H.FirstIndex ≤ 4*t*H.q := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _ : Fin H.q, 4*t := sum_le_sum (fun i _ => by simpa using H.first_count i)
    _ = _ := by simp [mul_comm]

lemma secondIndex_card (H : History G t) : Fintype.card H.SecondIndex ≤ 2*t*H.q := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _ : Fin H.q, 2*t := sum_le_sum (fun i _ => by simpa using H.second_count i)
    _ = _ := by simp [mul_comm]

end History
end LinearListHadwiger.Footprint

namespace LinearListHadwiger.Footprint.History
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t : ℕ}

abbrev FirstPast (H : History G t) (r : ℕ) := {i : H.FirstIndex // i.1.val < r}
abbrev SecondPast (H : History G t) (r : ℕ) := {i : H.SecondIndex // i.1.val < r}

lemma firstPast_subset (H : History G t) {r : ℕ} (hr : r ≤ H.q) (i : H.FirstPast r) :
    H.firstPath i.val ⊆ H.footprint r :=
  (H.firstPath_next i.val).trans (H.footprint_mono (by omega) hr)

lemma secondPast_subset (H : History G t) {r : ℕ} (hr : r ≤ H.q) (i : H.SecondPast r) :
    H.secondPath i.val ⊆ H.footprint r :=
  (H.secondPath_next i.val).trans (H.footprint_mono (by omega) hr)

lemma firstPast_card (H : History G t) (r : ℕ) : Fintype.card (H.FirstPast r) ≤ 4*t*H.q :=
  (Fintype.card_subtype_le _).trans H.firstIndex_card

lemma secondPast_card (H : History G t) (r : ℕ) : Fintype.card (H.SecondPast r) ≤ 2*t*H.q :=
  (Fintype.card_subtype_le _).trans H.secondIndex_card

noncomputable def firstException (H : History G t) (r : ℕ) : Finset V :=
  exceptional G (fun i : H.FirstPast r => H.firstPath i.val) (H.footprint r) t
noncomputable def secondException (H : History G t) (r : ℕ) : Finset V :=
  exceptional G (fun i : H.SecondPast r => H.secondPath i.val) (H.footprint r) t

lemma exceptions_card : ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (H : History G t),
    hadwigerNumber G < t → ∀ r ≤ H.q,
    ((H.firstException r ∪ H.secondException r).card : ℝ) ≤
      6*(H.q:ℝ)*(t:ℝ)^(101/100:ℝ) := by
  classical
  obtain ⟨t₀,ht₀⟩ := exceptional_card
  refine ⟨max t₀ 1,?_⟩
  intro t ht V _ _ G H hex r hr
  have ht' : t₀ ≤ t := (le_max_left _ _).trans ht
  have htp : (0:ℝ) < t := by
    exact_mod_cast (Nat.zero_lt_of_lt ((le_max_right t₀ 1).trans ht))
  have hA := ht₀ t ht' V (H.FirstPast r) G (fun i => H.firstPath i.val)
    (H.footprint r) hex (fun i => H.firstPath_connected i.val)
    (fun i j hij => H.firstPath_disjoint i.val j.val (fun he => hij (Subtype.ext he)))
    (H.firstPast_subset hr)
  have hB := ht₀ t ht' V (H.SecondPast r) G (fun i => H.secondPath i.val)
    (H.footprint r) hex (fun i => H.secondPath_connected i.val)
    (fun i j hij => H.secondPath_disjoint i.val j.val (fun he => hij (Subtype.ext he)))
    (H.secondPast_subset hr)
  have hAc : (Fintype.card (H.FirstPast r) : ℝ) ≤ 4*t*H.q := by
    exact_mod_cast H.firstPast_card r
  have hBc : (Fintype.card (H.SecondPast r) : ℝ) ≤ 2*t*H.q := by
    exact_mod_cast H.secondPast_card r
  calc
    _ ≤ ((H.firstException r).card : ℝ) + (H.secondException r).card := by
      exact_mod_cast card_union_le (H.firstException r) (H.secondException r)
    _ ≤ (t:ℝ)^(1/100:ℝ)*(4*t*H.q)+(t:ℝ)^(1/100:ℝ)*(2*t*H.q) :=
      add_le_add (hA.trans (mul_le_mul_of_nonneg_left hAc (by positivity)))
        (hB.trans (mul_le_mul_of_nonneg_left hBc (by positivity)))
    _ = _ := by
      have he : (t:ℝ)^(101/100:ℝ) = (t:ℝ)^(1/100:ℝ)*t := by
        rw [←Real.rpow_add_one htp.ne']; norm_num
      rw [he]; ring

noncomputable def small (H : History G t) : Finset V :=
  H.footprint 0 ∪ univ.biUnion (fun i : Fin H.q =>
    H.district i ∪ H.junction i ∪ H.tips i ∪ (H.first i).starts ∪
      (H.first i).ends ∪ (H.second i).starts ∪ (H.second i).ends)

lemma small_round_card (H : History G t) (i : Fin H.q) :
    ((H.district i ∪ H.junction i ∪ H.tips i ∪ (H.first i).starts ∪
      (H.first i).ends ∪ (H.second i).starts ∪ (H.second i).ends).card : ℝ) ≤
      2*(t:ℝ)^(106/100:ℝ)+13*t := by
  have h1 : ((H.first i).starts.card : ℝ) ≤ 4*t := by
    exact_mod_cast ((H.first i).starts_card.trans (H.first_count i))
  have h2 : ((H.first i).ends.card : ℝ) ≤ 4*t := by
    exact_mod_cast ((H.first i).ends_card.trans (H.first_count i))
  have h3 : ((H.second i).starts.card : ℝ) ≤ 2*t := by
    exact_mod_cast ((H.second i).starts_card.trans (H.second_count i))
  have h4 : ((H.second i).ends.card : ℝ) ≤ 2*t := by
    exact_mod_cast ((H.second i).ends_card.trans (H.second_count i))
  have h5 : ((H.tips i).card : ℝ) ≤ t := by exact_mod_cast H.tips_card i
  have hu (A B : Finset V) : ((A ∪ B).card : ℝ) ≤ A.card+B.card := by
    exact_mod_cast card_union_le A B
  calc
    _ ≤ ((((((H.district i).card : ℝ)+(H.junction i).card)+(H.tips i).card)+
        (H.first i).starts.card)+(H.first i).ends.card)+(H.second i).starts.card+
        (H.second i).ends.card := by
      linarith only [hu (H.district i) (H.junction i),
        hu (H.district i ∪ H.junction i) (H.tips i),
        hu (H.district i ∪ H.junction i ∪ H.tips i) (H.first i).starts,
        hu (H.district i ∪ H.junction i ∪ H.tips i ∪ (H.first i).starts) (H.first i).ends,
        hu (H.district i ∪ H.junction i ∪ H.tips i ∪ (H.first i).starts ∪ (H.first i).ends)
          (H.second i).starts,
        hu (H.district i ∪ H.junction i ∪ H.tips i ∪ (H.first i).starts ∪ (H.first i).ends ∪
          (H.second i).starts) (H.second i).ends]
    _ ≤ _ := by linarith [H.district_card i,H.junction_card i]

lemma small_card (H : History G t) : (H.small.card : ℝ) ≤
    2*(H.q:ℝ)*(t:ℝ)^(106/100:ℝ)+(13*(H.q:ℝ)+1)*t := by
  have hf : ((H.footprint 0).card : ℝ) ≤ t := by exact_mod_cast H.initial_card
  have hu := card_union_le (H.footprint 0) (univ.biUnion (fun i : Fin H.q =>
    H.district i ∪ H.junction i ∪ H.tips i ∪ (H.first i).starts ∪
      (H.first i).ends ∪ (H.second i).starts ∪ (H.second i).ends))
  have hb := card_biUnion_le (s := (univ : Finset (Fin H.q)))
    (t := fun i => H.district i ∪ H.junction i ∪ H.tips i ∪ (H.first i).starts ∪
      (H.first i).ends ∪ (H.second i).starts ∪ (H.second i).ends)
  have hu' : (H.small.card : ℝ) ≤ (H.footprint 0).card+
      ∑ i : Fin H.q, ((H.district i ∪ H.junction i ∪ H.tips i ∪ (H.first i).starts ∪
      (H.first i).ends ∪ (H.second i).starts ∪ (H.second i).ends).card : ℝ) := by
    exact_mod_cast hu.trans (Nat.add_le_add_left hb _)
  have hs := sum_le_sum (s := (univ : Finset (Fin H.q))) (fun i _ => H.small_round_card i)
  have hs' : (∑ i : Fin H.q, ((H.district i ∪ H.junction i ∪ H.tips i ∪ (H.first i).starts ∪
      (H.first i).ends ∪ (H.second i).starts ∪ (H.second i).ends).card : ℝ)) ≤
      (H.q:ℝ)*(2*(t:ℝ)^(106/100:ℝ)+13*t) := by simpa [mul_add] using hs
  nlinarith

noncomputable def deleted (H : History G t) : Finset V :=
  H.small ∪ (univ.biUnion (fun r : Fin (H.q+1) => H.firstException r ∪ H.secondException r))

lemma deleted_card : ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (H : History G t),
    hadwigerNumber G < t →
    (H.deleted.card : ℝ) ≤ 2*(H.q:ℝ)*(t:ℝ)^(106/100:ℝ)+(13*(H.q:ℝ)+1)*t+
      6*(H.q:ℝ)*((H.q:ℝ)+1)*(t:ℝ)^(101/100:ℝ) := by
  classical
  obtain ⟨t₀,ht₀⟩ := exceptions_card
  refine ⟨t₀,?_⟩
  intro t ht V _ _ G H hex
  have hu := card_union_le H.small (univ.biUnion
    (fun r : Fin (H.q+1) => H.firstException r ∪ H.secondException r))
  have hb := card_biUnion_le (s := (univ : Finset (Fin (H.q+1))))
    (t := fun r => H.firstException r ∪ H.secondException r)
  have hu' : (H.deleted.card : ℝ) ≤ H.small.card+
      ∑ r : Fin (H.q+1), ((H.firstException r ∪ H.secondException r).card : ℝ) := by
    exact_mod_cast hu.trans (Nat.add_le_add_left hb _)
  have hs := sum_le_sum (s := (univ : Finset (Fin (H.q+1))))
    (fun r _ => ht₀ t ht V G H hex r.val (by omega))
  have hs' : (∑ r : Fin (H.q+1), ((H.firstException r ∪ H.secondException r).card : ℝ)) ≤
      ((H.q:ℝ)+1)*(6*(H.q:ℝ)*(t:ℝ)^(101/100:ℝ)) := by simpa [mul_add] using hs
  nlinarith [H.small_card]

end LinearListHadwiger.Footprint.History

namespace LinearListHadwiger.Footprint
open Finset
attribute [local instance] Classical.propDecidable

lemma degenerate_union {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) (d a b : ℕ) (hA : DegenerateOn G A d)
    (hB : DegenerateOn G B a) (hback : ∀ v ∈ B, (A.filter (G.Adj v)).card ≤ b)
    (hab : a+b ≤ d) : DegenerateOn G (A ∪ B) d := by
  intro T hT hn
  by_cases hnew : (T ∩ B).Nonempty
  · obtain ⟨v,hv,hd⟩ := hB (T ∩ B) inter_subset_right hnew
    have hvB := (mem_inter.mp hv).2
    have hsub : T.filter (G.Adj v) ⊆ ((T ∩ B).filter (G.Adj v)) ∪ (A.filter (G.Adj v)) := by
      intro w hw
      obtain ⟨hwT,hadj⟩ := mem_filter.mp hw
      rcases mem_union.mp (hT hwT) with hwA | hwB
      · exact mem_union_right _ (mem_filter.mpr ⟨hwA,hadj⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_inter.mpr ⟨hwT,hwB⟩,hadj⟩)
    refine ⟨v,(mem_inter.mp hv).1,?_⟩
    exact (card_le_card hsub).trans ((card_union_le _ _).trans
      ((Nat.add_le_add hd (hback v hvB)).trans hab))
  · apply hA T ?_ hn
    intro v hv
    rcases mem_union.mp (hT hv) with hvA | hvB
    · exact hvA
    · exact False.elim (hnew ⟨v,mem_inter.mpr ⟨hv,hvB⟩⟩)

namespace History
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t : ℕ}

lemma initial_small (H : History G t) : H.footprint 0 ⊆ H.small := subset_union_left

lemma round_small (H : History G t) (i : Fin H.q) :
    H.district i ∪ H.junction i ∪ H.tips i ∪ (H.first i).starts ∪
      (H.first i).ends ∪ (H.second i).starts ∪ (H.second i).ends ⊆ H.small := by
  intro v hv
  exact mem_union_right _ (mem_biUnion.mpr ⟨i,mem_univ _,hv⟩)

lemma district_small (H : History G t) (i : Fin H.q) : H.district i ⊆ H.small := by
  intro v hv; apply H.round_small i
  simp only [mem_union]; tauto
lemma junction_small (H : History G t) (i : Fin H.q) : H.junction i ⊆ H.small := by
  intro v hv; apply H.round_small i
  simp only [mem_union]; tauto
lemma first_starts_small (H : History G t) (i : Fin H.q) : (H.first i).starts ⊆ H.small := by
  intro v hv; apply H.round_small i
  simp only [mem_union]; tauto

lemma small_deleted (H : History G t) : H.small ⊆ H.deleted := subset_union_left

lemma footprint_path (H : History G t) {r : ℕ} (hr : r ≤ H.q) {v : V}
    (hv : v ∈ H.footprint r) (hsmall : v ∉ H.small) :
    (∃ i : H.FirstPast r, v ∈ H.firstPath i.val) ∨
      (∃ i : H.SecondPast r, v ∈ H.secondPath i.val) := by
  induction r with
  | zero => exact False.elim (hsmall (H.initial_small hv))
  | succ r ih =>
    let j : Fin H.q := ⟨r,by omega⟩
    rw [H.next j] at hv
    rcases mem_union.mp hv with hv | hv2
    · rcases mem_union.mp hv with hv | hv1
      · rcases mem_union.mp hv with hv | hvJ
        · rcases mem_union.mp hv with hvF | hvD
          · rcases ih (by omega) hvF with ⟨i,hi⟩ | ⟨i,hi⟩
            · exact Or.inl ⟨⟨i.val,by have := i.property; omega⟩,hi⟩
            · exact Or.inr ⟨⟨i.val,by have := i.property; omega⟩,hi⟩
          · exact False.elim (hsmall (H.district_small j hvD))
        · exact False.elim (hsmall (H.junction_small j hvJ))
      · rw [(H.first j).used_eq] at hv1
        obtain ⟨i,_,hi⟩ := mem_biUnion.mp hv1
        left
        refine ⟨⟨⟨j,i⟩,by dsimp [j]; omega⟩,mem_sdiff.mpr ⟨hi,?_⟩⟩
        intro he
        have he' := mem_singleton.mp he
        exact hsmall (H.first_starts_small j (mem_image.mpr ⟨i,mem_univ _,he'.symm⟩))
    · rw [(H.second j).used_eq] at hv2
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp hv2
      exact Or.inr ⟨⟨⟨j,i⟩,by dsimp [j]; omega⟩,hi⟩

lemma first_exception_deleted (H : History G t) {r : ℕ} (hr : r ≤ H.q) :
    H.firstException r ⊆ H.deleted := by
  intro v hv
  exact mem_union_right _ (mem_biUnion.mpr ⟨⟨r,by omega⟩,mem_univ _,mem_union_left _ hv⟩)
lemma second_exception_deleted (H : History G t) {r : ℕ} (hr : r ≤ H.q) :
    H.secondException r ⊆ H.deleted := by
  intro v hv
  exact mem_union_right _ (mem_biUnion.mpr ⟨⟨r,by omega⟩,mem_univ _,mem_union_right _ hv⟩)

lemma first_nonexceptional (H : History G t) {r : ℕ} (hr : r ≤ H.q) {v : V}
    (hv : v ∉ H.footprint r) (hx : v ∉ H.deleted) :
    (univ.filter (fun i : H.FirstPast r => ∃ w ∈ H.firstPath i.val, G.Adj v w)).card ≤ 3202*t := by
  apply Nat.le_of_lt
  apply Nat.lt_of_not_ge
  intro hle
  exact hx (H.first_exception_deleted hr (mem_filter.mpr ⟨mem_univ _,hv,hle⟩))
lemma second_nonexceptional (H : History G t) {r : ℕ} (hr : r ≤ H.q) {v : V}
    (hv : v ∉ H.footprint r) (hx : v ∉ H.deleted) :
    (univ.filter (fun i : H.SecondPast r => ∃ w ∈ H.secondPath i.val, G.Adj v w)).card ≤ 3202*t := by
  apply Nat.le_of_lt
  apply Nat.lt_of_not_ge
  intro hle
  exact hx (H.second_exception_deleted hr (mem_filter.mpr ⟨mem_univ _,hv,hle⟩))

lemma first_past_neighbors (H : History G t) {r : ℕ} (hr : r ≤ H.q) {v : V}
    (hv : v ∉ H.footprint r) (i : H.FirstPast r) :
    ((H.firstPath i.val).filter (G.Adj v)).card ≤ 3 := by
  let j := i.val.1
  have hj : j.val+1 ≤ r := by have := i.property; dsimp [j]; omega
  have hnot : v ∉ H.footprint j.val := fun hh => hv (H.footprint_mono (by omega) hr hh)
  have hdomain : v ∈ (H.first j).domain := by
    rw [H.first_domain j]
    exact mem_sdiff.mpr ⟨mem_univ _,fun hh => hnot (mem_sdiff.mp hh).1⟩
  have hout : v ∉ (H.first j).used := fun hh => hv
    (H.footprint_mono hj hr (H.first_used_next j hh))
  exact (card_le_card (filter_subset_filter _ sdiff_subset)).trans
    ((H.first j).path_neighbors i.val.2 v hdomain hout)

lemma second_past_neighbors (H : History G t) {r : ℕ} (hr : r ≤ H.q) {v : V}
    (hv : v ∉ H.footprint r) (i : H.SecondPast r) :
    ((H.secondPath i.val).filter (G.Adj v)).card ≤ 3 := by
  let j := i.val.1
  have hj : j.val+1 ≤ r := by have := i.property; dsimp [j]; omega
  have hdomain : v ∈ (H.second j).domain := by
    rw [H.second_domain j]
    refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact hv (H.footprint_mono (by omega) hr hh)
    · exact hv (H.footprint_mono hj hr (H.roots_next j hh))
  have hout : v ∉ (H.second j).used := fun hh => hv
    (H.footprint_mono hj hr (H.second_used_next j hh))
  exact (H.second j).path_neighbors i.val.2 v hdomain hout

lemma past_neighbors (H : History G t) {r : ℕ} (hr : r ≤ H.q) {v : V}
    (hv : v ∉ H.footprint r) (hx : v ∉ H.deleted) :
    ((H.footprint r \ H.deleted).filter (G.Adj v)).card ≤ 6*3202*t := by
  let A := univ.biUnion (fun i : H.FirstPast r => H.firstPath i.val)
  let B := univ.biUnion (fun i : H.SecondPast r => H.secondPath i.val)
  have hA : (A.filter (G.Adj v)).card ≤ 3*(3202*t) :=
    neighbors_in_collection G _ v _ _ (H.first_past_neighbors hr hv) (H.first_nonexceptional hr hv hx)
  have hB : (B.filter (G.Adj v)).card ≤ 3*(3202*t) :=
    neighbors_in_collection G _ v _ _ (H.second_past_neighbors hr hv) (H.second_nonexceptional hr hv hx)
  have hsub : H.footprint r \ H.deleted ⊆ A ∪ B := by
    intro w hw
    obtain ⟨hw,hn⟩ := mem_sdiff.mp hw
    rcases H.footprint_path hr hw (fun hh => hn (H.small_deleted hh)) with ⟨i,hi⟩ | ⟨i,hi⟩
    · exact mem_union_left _ (mem_biUnion.mpr ⟨i,mem_univ _,hi⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨i,mem_univ _,hi⟩)
  calc
    _ ≤ ((A ∪ B).filter (G.Adj v)).card := card_le_card (filter_subset_filter _ hsub)
    _ ≤ (A.filter (G.Adj v)).card+(B.filter (G.Adj v)).card := by
      rw [filter_union]; exact card_union_le _ _
    _ ≤ _ := by omega

end History
end LinearListHadwiger.Footprint

end OAI
