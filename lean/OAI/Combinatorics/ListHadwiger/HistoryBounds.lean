import OAI.Combinatorics.ListHadwiger.History

namespace OAI

namespace LinearListHadwiger.Footprint.History
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t : ℕ}

noncomputable def firstPhase (H : History G t) (i : Fin H.q) : Finset V :=
  ((H.first i).used \ H.footprint i.val) \ H.deleted
noncomputable def secondPhase (H : History G t) (i : Fin H.q) : Finset V :=
  ((H.second i).used \ (H.footprint i.val ∪ (H.first i).used)) \ H.deleted

lemma phase_decomposition (H : History G t) (i : Fin H.q) :
    H.footprint (i.val+1) \ H.deleted =
      ((H.footprint i.val \ H.deleted) ∪ H.firstPhase i) ∪ H.secondPhase i := by
  ext v
  have hD : v ∈ H.district i → v ∈ H.deleted := fun h => H.small_deleted (H.district_small i h)
  have hJ : v ∈ H.junction i → v ∈ H.deleted := fun h => H.small_deleted (H.junction_small i h)
  rw [H.next i]
  simp only [firstPhase,secondPhase,mem_sdiff,mem_union]
  tauto

lemma firstPhase_degenerate (H : History G t) (i : Fin H.q) :
    DegenerateOn G (H.firstPhase i) (8*t) := by
  intro T hT hn
  obtain ⟨v,hv,hd⟩ := (H.first i).degenerate T (hT.trans (sdiff_subset.trans sdiff_subset)) hn
  exact ⟨v,hv,hd.trans (by have := H.first_count i; omega)⟩

lemma secondPhase_degenerate (H : History G t) (i : Fin H.q) :
    DegenerateOn G (H.secondPhase i) (8*t) := by
  intro T hT hn
  obtain ⟨v,hv,hd⟩ := (H.second i).degenerate T (hT.trans (sdiff_subset.trans sdiff_subset)) hn
  exact ⟨v,hv,hd.trans (by have := H.second_count i; omega)⟩

lemma secondPhase_first_neighbors (H : History G t) (i : Fin H.q) {v : V}
    (hv : v ∈ H.secondPhase i) : ((H.firstPhase i).filter (G.Adj v)).card ≤ 12*t := by
  obtain ⟨⟨_,hv⟩,_⟩ := mem_sdiff.mp hv |>.imp_left mem_sdiff.mp
  have hF : v ∉ H.footprint i.val := fun hh => hv (mem_union_left _ hh)
  have hp : v ∉ (H.first i).used := fun hh => hv (mem_union_right _ hh)
  have hd : v ∈ (H.first i).domain := by
    rw [H.first_domain i]
    exact mem_sdiff.mpr ⟨mem_univ _,fun hh => hF (mem_sdiff.mp hh).1⟩
  exact (card_le_card (filter_subset_filter _ (sdiff_subset.trans sdiff_subset))).trans
    (((H.first i).used_neighbors v hd hp).trans (by have := H.first_count i; omega))

lemma footprint_degenerate (H : History G t) {r : ℕ} (hr : r ≤ H.q) :
    DegenerateOn G (H.footprint r \ H.deleted) ((6*3202+20)*t) := by
  induction r with
  | zero =>
    intro T hT hn
    obtain ⟨v,hv⟩ := hn
    obtain ⟨hvF,hvX⟩ := mem_sdiff.mp (hT hv)
    exact False.elim (hvX (H.small_deleted (H.initial_small hvF)))
  | succ r ih =>
    let i : Fin H.q := ⟨r,by omega⟩
    have hfirst : DegenerateOn G ((H.footprint r \ H.deleted) ∪ H.firstPhase i)
        ((6*3202+20)*t) := by
      apply degenerate_union G _ _ _ (8*t) (6*3202*t) (ih (by omega)) (H.firstPhase_degenerate i)
      · intro v hv
        obtain ⟨⟨_,hvF⟩,hvX⟩ := mem_sdiff.mp hv |>.imp_left mem_sdiff.mp
        exact H.past_neighbors (by omega) hvF hvX
      · omega
    rw [H.phase_decomposition i]
    apply degenerate_union G _ _ _ (8*t) (6*3202*t+12*t) hfirst (H.secondPhase_degenerate i)
    · intro v hv
      obtain ⟨⟨_,hvF⟩,hvX⟩ := mem_sdiff.mp hv |>.imp_left mem_sdiff.mp
      have hF : v ∉ H.footprint r := fun hh => hvF (mem_union_left _ hh)
      have h1 := H.past_neighbors (by omega : r ≤ H.q) hF hvX
      have h2 := H.secondPhase_first_neighbors i hv
      rw [filter_union]
      exact (card_union_le _ _).trans (Nat.add_le_add h1 h2)
    · omega

lemma footprint_external_neighbors (H : History G t) {v : V}
    (hv : v ∉ H.deleted ∪ (H.footprint H.q \ H.deleted)) :
    ((H.footprint H.q \ H.deleted).filter (G.Adj v)).card ≤ (6*3202+20)*t := by
  have hx : v ∉ H.deleted := fun h => hv (mem_union_left _ h)
  have hF : v ∉ H.footprint H.q := fun h => hv (mem_union_right _ (mem_sdiff.mpr ⟨h,hx⟩))
  exact (H.past_neighbors le_rfl hF hx).trans (by omega)

theorem footprint_deletion_data : ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (H : History G t),
    hadwigerNumber G < t → H.q ≤ rounds t →
    (H.deleted.card : ℝ) ≤ (t:ℝ)^(11/10:ℝ) ∧
    Disjoint H.deleted (H.footprint H.q \ H.deleted) ∧
    DegenerateOn G (H.footprint H.q \ H.deleted) ((6*3202+20)*t) ∧
    (∀ v ∉ H.deleted ∪ (H.footprint H.q \ H.deleted),
      ((H.footprint H.q \ H.deleted).filter (G.Adj v)).card ≤ (6*3202+20)*t) := by
  classical
  obtain ⟨t₁,ht₁⟩ := deleted_card
  obtain ⟨T,hT⟩ := Filter.eventually_atTop.mp exceptional_size_cutoff
  refine ⟨max t₁ ⌈T⌉₊,?_⟩
  intro t ht V _ _ G H hex hround
  have ht₁' : t₁ ≤ t := (le_max_left _ _).trans ht
  have hT' : T ≤ (t:ℝ) := (Nat.le_ceil T).trans (by exact_mod_cast (le_max_right _ _).trans ht)
  have hc := (hT t hT').2.2
  have hq : (H.q:ℝ) ≤ rounds (t:ℝ) := by exact_mod_cast hround
  refine ⟨?_,disjoint_sdiff_self_right,H.footprint_degenerate le_rfl,fun v hv => H.footprint_external_neighbors hv⟩
  apply (ht₁ t ht₁' V G H hex).trans
  apply le_trans ?_ hc
  gcongr

end LinearListHadwiger.Footprint.History

namespace LinearListHadwiger.SmallList
open Finset

attribute [local instance] Classical.propDecidable

theorem additive_deletion_or_obstruction : ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (X Y : Finset V) (d : ℕ),
    hadwigerNumber G < t → (X.card:ℝ) ≤ (t:ℝ)^(11/10:ℝ) → Disjoint X Y →
    DegenerateOn G Y (d*t) →
    (∀ v ∉ X∪Y, (Y.filter (G.Adj v)).card ≤ d*t) →
    listChromaticNumber G ≤ listChromaticNumber (G.induce (↑(univ\(X∪Y)):Set V)) +
      (4*32768+d+5)*t ∨ FractionalObstruction G := by
  classical
  obtain ⟨T,hT⟩ := choosable_or_fractional_obstruction
  obtain ⟨t₁,ht₁⟩ := reservation_cutoff_minor
  refine ⟨max 1 (max ⌈T⌉₊ t₁),?_⟩
  intro t ht V _ _ G X Y d hminor hsize hXY hY hRY
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have htT : T ≤ (t:ℝ) := (Nat.le_ceil T).trans (by
    exact_mod_cast ((le_max_left ⌈T⌉₊ t₁).trans (le_max_right 1 _)).trans ht)
  have htt : t₁ ≤ t := ((le_max_right ⌈T⌉₊ t₁).trans (le_max_right 1 _)).trans ht
  have hord : (Fintype.card (↑X:Set V):ℝ) ≤ (t:ℝ)^(11/10:ℝ) := by
    rw [show Fintype.card (↑X:Set V)=X.card from Fintype.card_coe X]
    exact hsize
  have hmin := (Knitting.model_induce G X).hadwiger_le.trans_lt hminor
  rcases hT t htT (↑X:Set V) (G.induce (↑X:Set V)) hord hmin with hsmall | hbad
  · left
    have hm : t ≤ 32768*t := by omega
    have htail := ht₁ t htt V G X (32768*t) hm hminor hsize
    have hh := additive_deletion_coloring G X Y ht1 hXY hsmall hY hRY
      (choosable_listChromaticNumber (G.induce (↑(univ\(X∪Y)):Set V))) htail
    have he : listChromaticNumber (G.induce (↑(univ\(X∪Y)):Set V)) +
        4*(32768*t)+d*t+5*t = listChromaticNumber (G.induce (↑(univ\(X∪Y)):Set V)) +
        (4*32768+d+5)*t := by ring
    rw [he] at hh
    exact (listChromaticNumber_le_iff G _).mpr hh
  · exact Or.inr (obstruction_induce G X hbad)

end LinearListHadwiger.SmallList

namespace LinearListHadwiger.Footprint.History
open Finset SmallList

theorem list_loss_or_obstruction : ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (H : History G t),
    hadwigerNumber G < t → H.q ≤ rounds t →
    listChromaticNumber G ≤ listChromaticNumber (G.induce (↑(univ\H.footprint H.q):Set V)) +
      (4*32768+6*3202+25)*t ∨ FractionalObstruction G := by
  classical
  obtain ⟨t₁,ht₁⟩ := footprint_deletion_data
  obtain ⟨t₂,ht₂⟩ := additive_deletion_or_obstruction
  refine ⟨max t₁ t₂,?_⟩
  intro t ht V _ _ G H hminor hround
  obtain ⟨hsize,hdis,hdeg,hext⟩ := ht₁ t ((le_max_left _ _).trans ht) V G H hminor hround
  rcases ht₂ t ((le_max_right _ _).trans ht) V G H.deleted
    (H.footprint H.q\H.deleted) (6*3202+20) hminor hsize hdis hdeg hext with hbound | hbad
  · left
    have hsub : (↑(univ\(H.deleted∪(H.footprint H.q\H.deleted))):Set V) ⊆
        (↑(univ\H.footprint H.q):Set V) := by
      intro v hv
      obtain ⟨hu,hn⟩ := mem_sdiff.mp hv
      refine mem_sdiff.mpr ⟨hu,?_⟩
      intro hh
      by_cases hx : v∈H.deleted
      · exact hn (mem_union_left _ hx)
      · exact hn (mem_union_right _ (mem_sdiff.mpr ⟨hh,hx⟩))
    have hmono := (listChromaticNumber_le_iff _ _).mpr
      (choosable_induce_subset
        (choosable_listChromaticNumber (G.induce (↑(univ\H.footprint H.q):Set V))) hsub)
    have he : 4*32768+(6*3202+20)+5=4*32768+6*3202+25 := by norm_num
    rw [he] at hbound
    exact hbound.trans (Nat.add_le_add_right hmono _)
  · exact Or.inr hbad

end LinearListHadwiger.Footprint.History

end OAI
