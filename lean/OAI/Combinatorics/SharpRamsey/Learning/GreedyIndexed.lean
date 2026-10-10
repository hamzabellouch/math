import Mathlib

namespace OAI

section
namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical
noncomputable section
variable {α β : Type*}

def residual (S : Finset α) (U : β → Finset α) : List β → Finset α
  | [] => S
  | b::bs => residual (S \ U b) U bs

def cells (S : Finset α) (U : β → Finset α) : List β → List (Finset α)
  | [] => []
  | b::bs => (S ∩ U b)::cells (S \ U b) U bs

inductive Complete (F : Finset β) (U : β → Finset α) (m : ℕ) : Finset α → List β → Prop
  | nil (S : Finset α) (h : ∀ b ∈ F, (S ∩ U b).card < m) : Complete F U m S []
  | cons (S : Finset α) (b : β) (bs : List β) (hb : b ∈ F)
      (hrich : m ≤ (S ∩ U b).card)
      (hmax : ∀ c ∈ F, (S ∩ U c).card ≤ (S ∩ U b).card)
      (tail : Complete F U m (S \ U b) bs) : Complete F U m S (b::bs)

theorem exists_complete (F : Finset β) (U : β → Finset α) (m : ℕ) (hm : 0 < m)
    (S : Finset α) : ∃ bs, Complete F U m S bs := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | h n ih =>
    by_cases hall : ∀ b ∈ F, (S ∩ U b).card < m
    · exact ⟨[],Complete.nil S hall⟩
    · have hex : ∃ c ∈ F, m ≤ (S ∩ U c).card := by
        push Not at hall
        exact hall
      obtain ⟨c,hc,hcm⟩ := hex
      obtain ⟨b,hb,hmax⟩ := exists_max_image F (fun b => (S ∩ U b).card) ⟨c,hc⟩
      have hrich := hcm.trans (hmax c hc)
      have hsmall : (S \ U b).card < n := by
        have he := card_sdiff_add_card_inter S (U b)
        omega
      obtain ⟨bs,hbs⟩ := ih (S \ U b).card hsmall (S \ U b) rfl
      exact ⟨b::bs,Complete.cons S b bs hb hrich hmax hbs⟩

lemma residual_subset (S : Finset α) (U : β → Finset α) (bs : List β) :
    residual S U bs ⊆ S := by
  induction bs generalizing S with
  | nil => exact subset_rfl
  | cons b bs ih => exact (ih _).trans sdiff_subset

lemma mem_cells_subset (S : Finset α) (U : β → Finset α) (bs : List β)
    (C : Finset α) (hC : C ∈ cells S U bs) : C ⊆ S := by
  induction bs generalizing S with
  | nil => simp [cells] at hC
  | cons b bs ih =>
    simp only [cells,List.mem_cons] at hC
    rcases hC with rfl | hC
    · exact inter_subset_left
    · exact (ih _ hC).trans sdiff_subset

lemma cells_length (S : Finset α) (U : β → Finset α) (bs : List β) :
    (cells S U bs).length = bs.length := by
  induction bs generalizing S with
  | nil => rfl
  | cons b bs ih => simp [cells,ih]

theorem card_partition (S : Finset α) (U : β → Finset α) (bs : List β) :
    ((cells S U bs).map Finset.card).sum + (residual S U bs).card = S.card := by
  induction bs generalizing S with
  | nil => simp [cells,residual]
  | cons b bs ih =>
    simp only [cells,residual,List.map_cons,List.sum_cons]
    have ht := ih (S \ U b)
    have he := card_sdiff_add_card_inter S (U b)
    omega

lemma disjoint_cells (S : Finset α) (U : β → Finset α) (bs : List β) :
    (cells S U bs).Pairwise Disjoint := by
  induction bs generalizing S with
  | nil => simp [cells]
  | cons b bs ih =>
    rw [cells,List.pairwise_cons]
    refine ⟨?_,ih _⟩
    intro C hC
    have hc := mem_cells_subset (S \ U b) U bs C hC
    apply disjoint_left.mpr
    intro x hx hxc
    exact (mem_sdiff.mp (hc hxc)).2 (mem_inter.mp hx).2

lemma complete_small_residual {F : Finset β} {U : β → Finset α} {m : ℕ}
    {S : Finset α} {bs : List β} (h : Complete F U m S bs) :
    ∀ b ∈ F, (residual S U bs ∩ U b).card < m := by
  induction h with
  | nil S ht => exact ht
  | cons S b bs hb hrich hmax htail ih => exact ih

lemma complete_length_bound {F : Finset β} {U : β → Finset α} {m : ℕ}
    {S : Finset α} {bs : List β} (h : Complete F U m S bs) :
    bs.length*m+(residual S U bs).card ≤ S.card := by
  induction h with
  | nil S ht => simp [residual]
  | cons S b bs hb hrich hmax htail ih =>
    simp only [List.length_cons,Nat.add_mul,one_mul,residual]
    have he := card_sdiff_add_card_inter S (U b)
    omega

lemma complete_cells_rich {F : Finset β} {U : β → Finset α} {m : ℕ}
    {S : Finset α} {bs : List β} (h : Complete F U m S bs) :
    ∀ C ∈ cells S U bs, m ≤ C.card := by
  induction h with
  | nil S ht => simp [cells]
  | cons S b bs hb hrich hmax htail ih =>
    intro C hC
    simp only [cells,List.mem_cons] at hC
    rcases hC with rfl | hc
    · exact hrich
    · exact ih C hc

lemma complete_cells_bounded {F : Finset β} {U : β → Finset α} {m : ℕ}
    {S : Finset α} {bs : List β} (h : Complete F U m S bs)
    (B : ℕ) (hB : ∀ b ∈ F, (S ∩ U b).card ≤ B) :
    ∀ C ∈ cells S U bs, C.card ≤ B := by
  induction h with
  | nil S ht => simp [cells]
  | cons S b bs hb hrich hmax htail ih =>
    intro C hC
    simp only [cells,List.mem_cons] at hC
    rcases hC with rfl | hc
    · exact hB b hb
    · apply ih (fun c hc => (card_le_card ?_).trans (hB c hc)) C hc
      exact inter_subset_inter_right sdiff_subset

theorem complete_nonincreasing {F : Finset β} {U : β → Finset α} {m : ℕ}
    {S : Finset α} {bs : List β} (h : Complete F U m S bs) :
    (cells S U bs).Pairwise (fun C D => D.card ≤ C.card) := by
  induction h with
  | nil S ht => simp [cells]
  | cons S b bs hb hrich hmax htail ih =>
    rw [cells,List.pairwise_cons]
    refine ⟨?_,ih⟩
    apply complete_cells_bounded htail
    intro c hc
    apply (card_le_card (inter_subset_inter_right (sdiff_subset (s:=S) (t:=U b)))).trans
    exact hmax c hc

end
end SharpLogRamsey.GreedyPreparation

namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical
noncomputable section
variable {α β : Type*}

def removed (S : Finset α) (U : β → Finset α) (bs : List β) : Finset α :=
  S \ residual S U bs

def own (S : Finset α) (U : β → Finset α) : List β → α → Finset α
  | [], _ => ∅
  | b::bs, x => if x ∈ U b then S ∩ U b else own (S \ U b) U bs x

lemma residual_eq (S : Finset α) (U : β → Finset α) (bs : List β) :
    residual S U bs = S \ bs.toFinset.biUnion U := by
  induction bs generalizing S with
  | nil => simp [residual]
  | cons b bs ih =>
    rw [residual,ih]
    ext x
    simp only [mem_sdiff,List.toFinset_cons,mem_biUnion,mem_insert]
    aesop

lemma removed_subset (S : Finset α) (U : β → Finset α) (bs : List β) :
    removed S U bs ⊆ S := sdiff_subset

lemma removed_eq (S : Finset α) (U : β → Finset α) (bs : List β) :
    removed S U bs = S ∩ bs.toFinset.biUnion U := by
  rw [removed,residual_eq]
  ext x
  simp only [mem_sdiff,mem_inter]
  tauto

lemma removed_cons (S : Finset α) (U : β → Finset α) (b : β) (bs : List β) :
    removed S U (b::bs) = (S ∩ U b) ∪ removed (S \ U b) U bs := by
  simp only [removed_eq,List.toFinset_cons,biUnion_insert]
  ext x
  simp only [mem_union,mem_inter,mem_sdiff]
  tauto

lemma cell_subset_removed (S : Finset α) (U : β → Finset α) (bs : List β)
    (C : Finset α) (hC : C ∈ cells S U bs) : C ⊆ removed S U bs := by
  induction bs generalizing S with
  | nil => simp [cells] at hC
  | cons b bs ih =>
    rw [removed_cons]
    simp only [cells,List.mem_cons] at hC
    rcases hC with rfl | hc
    · exact subset_union_left
    · exact (ih _ hc).trans subset_union_right

lemma own_empty_or_cell (S : Finset α) (U : β → Finset α) (bs : List β) (x : α) :
    own S U bs x = ∅ ∨ own S U bs x ∈ cells S U bs := by
  induction bs generalizing S with
  | nil => exact Or.inl rfl
  | cons b bs ih =>
    rw [own]
    split_ifs with hx
    · exact Or.inr (by simp [cells])
    · rcases ih (S \ U b) with hh | hh
      · exact Or.inl hh
      · exact Or.inr (by simp only [cells,List.mem_cons]; exact Or.inr hh)

lemma own_subset_removed (S : Finset α) (U : β → Finset α) (bs : List β) (x : α) :
    own S U bs x ⊆ removed S U bs := by
  rcases own_empty_or_cell S U bs x with hh | hh
  · rw [hh]; exact empty_subset _
  · exact cell_subset_removed S U bs _ hh

lemma own_card_le (S : Finset α) (U : β → Finset α) (bs : List β) (x : α)
    (B : ℕ) (hB : ∀ C ∈ cells S U bs, C.card ≤ B) :
    (own S U bs x).card ≤ B := by
  rcases own_empty_or_cell S U bs x with hh | hh
  · simp [hh]
  · exact hB _ hh

lemma removed_card (S : Finset α) (U : β → Finset α) (bs : List β) :
    (removed S U bs).card + (residual S U bs).card = S.card :=
  card_sdiff_add_card_eq_card (residual_subset S U bs)

lemma removed_card_eq_sum (S : Finset α) (U : β → Finset α) (bs : List β) :
    (removed S U bs).card = ((cells S U bs).map Finset.card).sum := by
  have h := removed_card S U bs
  have h' := card_partition S U bs
  omega

theorem preparation (F : Finset β) (U : β → Finset α) (m : ℕ) (hm : 0 < m)
    (S : Finset α) :
    (∃ S' : Finset α, S' ⊆ S ∧ S.card ≤ 2*S'.card ∧
      ∀ b ∈ F, (S' ∩ U b).card < m) ∨
    (∃ bs : List β, Complete F U m S bs ∧ S.card ≤ 2*(removed S U bs).card ∧
      bs.length*m ≤ S.card ∧
      (cells S U bs).Pairwise (fun C D => D.card ≤ C.card)) := by
  obtain ⟨bs,hbs⟩ := exists_complete F U m hm S
  by_cases hh : S.card ≤ 2*(removed S U bs).card
  · refine Or.inr ⟨bs,hbs,hh,?_,complete_nonincreasing hbs⟩
    have := complete_length_bound hbs
    omega
  · refine Or.inl ⟨residual S U bs,residual_subset S U bs,?_,complete_small_residual hbs⟩
    have := removed_card S U bs
    omega

lemma removed_inter_card_le (S : Finset α) (U : β → Finset α) (bs : List β)
    (L : Finset α) (hL : ∀ b ∈ bs, (U b ∩ L).card ≤ 1) :
    (removed S U bs ∩ L).card ≤ bs.length := by
  induction bs generalizing S with
  | nil => simp [removed,residual]
  | cons b bs ih =>
    rw [removed_cons,union_inter_distrib_right]
    apply (card_union_le _ _).trans
    have h1 : (S ∩ U b ∩ L).card ≤ 1 :=
      (card_le_card (inter_subset_inter_right inter_subset_right)).trans (hL b (by simp))
    have h2 := ih (S \ U b) (fun c hc => hL c (by simp [hc]))
    simpa only [List.length_cons] using Nat.add_le_add h1 h2 |>.trans_eq (Nat.add_comm 1 bs.length)

lemma outside_first_inter_empty (S : Finset α) (U : β → Finset α) (b : β)
    (bs : List β) (L : Finset α) (hL : L ⊆ U b) (x : α) (hx : x ∈ L) :
    ((removed S U (b::bs) \ own S U (b::bs) x) ∩ L) = ∅ := by
  rw [own,ite_eq_left (hL hx),removed_cons]
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨hy,hyL⟩ := mem_inter.mp hy
  obtain ⟨hy,hyn⟩ := mem_sdiff.mp hy
  rcases mem_union.mp hy with hh | hh
  · exact hyn hh
  · have hyS := removed_subset (S \ U b) U bs hh
    exact (mem_sdiff.mp hyS).2 (hL hyL)

lemma outside_inter_prefix (S : Finset α) (U : β → Finset α) (pre : List β)
    (b : β) (post : List β) (L : Finset α) (hL : L ⊆ U b)
    (x : α) (hx : x ∈ L) (hpre : ∀ c ∈ pre, x ∉ U c)
    (hline : ∀ c ∈ pre, (U c ∩ L).card ≤ 1) :
    ((removed S U (pre ++ b::post) \ own S U (pre ++ b::post) x) ∩ L).card ≤ pre.length := by
  induction pre generalizing S with
  | nil => simp only [List.nil_append,outside_first_inter_empty S U b post L hL x hx,card_empty,List.length_nil]
           exact le_rfl
  | cons c pre ih =>
    simp only [List.cons_append,own,ite_eq_right (hpre c (by simp))]
    rw [removed_cons]
    have hsubset : (((S ∩ U c) ∪ removed (S \ U c) U (pre ++ b::post)) \
        own (S \ U c) U (pre ++ b::post) x) ∩ L ⊆
      (S ∩ U c ∩ L) ∪ ((removed (S \ U c) U (pre ++ b::post) \
        own (S \ U c) U (pre ++ b::post) x) ∩ L) := by
      intro y hy
      simp only [mem_inter,mem_union,mem_sdiff] at hy ⊢
      tauto
    apply (card_le_card hsubset).trans ((card_union_le _ _).trans ?_)
    have h1 : (S ∩ U c ∩ L).card ≤ 1 :=
      (card_le_card (inter_subset_inter_right inter_subset_right)).trans (hline c (by simp))
    have h2 := ih (S \ U c) (fun e he => hpre e (by simp [he]))
      (fun e he => hline e (by simp [he]))
    simp only [List.length_cons]
    omega

end
end SharpLogRamsey.GreedyPreparation

namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*}

lemma residual_append (S : Finset α) (U : β → Finset α) (a b : List β) :
    residual S U (a++b) = residual (residual S U a) U b := by
  induction a generalizing S with
  | nil => rfl
  | cons x xs ih => simpa only [List.cons_append,residual] using ih (S \ U x)

lemma residual_nil (S : Finset α) (U : β → Finset α) : residual S U [] = S := rfl

lemma removed_append (S : Finset α) (U : β → Finset α) (a b : List β) :
    removed S U (a++b) = removed S U a ∪ removed (residual S U a) U b := by
  rw [removed,residual_append,removed,removed]
  have h1 := residual_subset S U a
  have h2 := residual_subset (residual S U a) U b
  ext x
  simp only [mem_sdiff,mem_union]
  constructor
  · intro hx
    by_cases hr : x ∈ residual S U a
    · exact Or.inr ⟨hr,hx.2⟩
    · exact Or.inl ⟨hx.1,hr⟩
  · rintro (hx|hx)
    · exact ⟨hx.1,fun hn => hx.2 (h2 hn)⟩
    · exact ⟨h1 hx.1,hx.2⟩

lemma own_append (S : Finset α) (U : β → Finset α) (a b : List β) (x : α)
    (ha : ∀ c ∈ a, x ∉ U c) : own S U (a++b) x = own (residual S U a) U b x := by
  induction a generalizing S with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.cons_append,own,ite_eq_right (ha c (by simp)),residual]
    exact ih (S \ U c) (fun d hd => ha d (by simp [hd]))

lemma cells_get (S : Finset α) (U : β → Finset α) (bs : List β)
    (i : ℕ) (hi : i < bs.length) :
    (cells S U bs)[i]'(by rw [cells_length]; exact hi) =
      residual S U (bs.take i) ∩ U bs[i] := by
  induction bs generalizing S i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [cells,List.getElem_cons_succ,List.take_succ_cons,residual]
      exact ih (S \ U b) i (by simpa using hi)

def indexedCell (S : Finset α) (U : β → Finset α) (bs : List β)
    (i : Fin bs.length) : Finset α := residual S U (bs.take i.val) ∩ U bs[i.val]

lemma indexedCell_eq (S : Finset α) (U : β → Finset α) (bs : List β)
    (i : Fin bs.length) : indexedCell S U bs i =
      (cells S U bs)[i.val]'(by rw [cells_length]; exact i.isLt) :=
  (cells_get S U bs i.val i.isLt).symm

lemma indexedCell_antitone {F : Finset β} {U : β → Finset α} {m : ℕ}
    {S : Finset α} {bs : List β} (h : Complete F U m S bs) :
    Antitone (fun i : Fin bs.length => (indexedCell S U bs i).card) := by
  intro i j hij
  change (indexedCell S U bs j).card ≤ (indexedCell S U bs i).card
  rw [indexedCell_eq,indexedCell_eq]
  by_cases he : i = j
  · subst j; exact le_rfl
  · have hlt : i.val < j.val := by
      have hne : i.val ≠ j.val := fun hh => he (Fin.ext hh)
      exact lt_of_le_of_ne hij hne
    exact (List.pairwise_iff_getElem.mp (complete_nonincreasing h))
      i.val j.val (by rw [cells_length]; exact i.isLt)
      (by rw [cells_length]; exact j.isLt) hlt

lemma indexedCell_sum (S : Finset α) (U : β → Finset α) (bs : List β) :
    ∑ i : Fin bs.length, (indexedCell S U bs i).card = (removed S U bs).card := by
  rw [removed_card_eq_sum]
  induction bs generalizing S with
  | nil => simp [cells]
  | cons b bs ih =>
    change (∑ i : Fin (bs.length+1), (indexedCell S U (b::bs) i).card) = _
    rw [Fin.sum_univ_succ]
    simp only [indexedCell,Fin.val_zero,List.take_zero,residual,List.getElem_cons_zero,
      Fin.val_succ,List.take_succ_cons,List.getElem_cons_succ,cells,List.map_cons,List.sum_cons]
    congr 1
    exact ih (S \ U b)

lemma residual_after_first_disjoint (S : Finset α) (U : β → Finset α)
    (b : β) (post : List β) (L : Finset α) (hL : L ⊆ U b) :
    Disjoint (removed (S \ U b) U post) L := by
  apply disjoint_left.mpr
  intro x hx hxL
  exact (mem_sdiff.mp (removed_subset (S \ U b) U post hx)).2 (hL hxL)

lemma removed_line_le_prefix_cell (S : Finset α) (U : β → Finset α)
    (pre : List β) (b : β) (post : List β) (L : Finset α) (hL : L ⊆ U b)
    (hpre : ∀ c ∈ pre, (U c ∩ L).card ≤ 1) :
    (removed S U (pre++b::post) ∩ L).card ≤
      pre.length + (residual S U pre ∩ U b ∩ L).card := by
  rw [removed_append,removed_cons,union_inter_distrib_right,
    union_inter_distrib_right]
  have he : removed (residual S U pre \ U b) U post ∩ L = ∅ :=
    disjoint_iff_inter_eq_empty.mp (residual_after_first_disjoint _ U b post L hL)
  rw [he,union_empty]
  exact (card_union_le _ _).trans (Nat.add_le_add_right
    (removed_inter_card_le S U pre L hpre) _)

lemma first_containing (U : β → Finset α) (bs : List β) (L : Finset α)
    (hex : ∃ b ∈ bs, L ⊆ U b) :
    ∃ pre b post, bs=pre++b::post ∧ L ⊆ U b ∧ ∀ c ∈ pre, ¬ L ⊆ U c := by
  induction bs with
  | nil => simp at hex
  | cons b bs ih =>
    by_cases hb : L ⊆ U b
    · exact ⟨[],b,bs,rfl,hb,by simp⟩
    · have hex' : ∃ c ∈ bs, L ⊆ U c := by
        obtain ⟨c,hc,hcL⟩ := hex
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact (hb hcL).elim
        · exact ⟨c,hc,hcL⟩
      obtain ⟨pre,c,post,he,hc,hpre⟩ := ih hex'
      refine ⟨b::pre,c,post,by simp [he],hc,?_⟩
      intro d hd
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact hb
      · exact hpre d hd

end
end SharpLogRamsey.GreedyPreparation

end

end OAI
