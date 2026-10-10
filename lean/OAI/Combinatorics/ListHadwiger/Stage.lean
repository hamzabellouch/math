import OAI.Combinatorics.ListHadwiger.HistoryBounds

namespace OAI

namespace LinearListHadwiger.Stage
open Finset
attribute [local instance] Classical.propDecidable
variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

noncomputable def ell (G : SimpleGraph V) (S : Finset V) : ℕ :=
  listChromaticNumber (G.induce (↑S : Set V))

omit [DecidableEq V] [DecidableEq W] in
lemma list_iso {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    listChromaticNumber G = listChromaticNumber H := by
  apply le_antisymm
  · exact (listChromaticNumber_le_iff _ _).mpr
      (choosable_of_iso e (choosable_listChromaticNumber H))
  · exact (listChromaticNumber_le_iff _ _).mpr
      (choosable_of_iso e.symm (choosable_listChromaticNumber G))

omit [Fintype W] [Fintype V] [DecidableEq W] in
lemma ell_image (G : SimpleGraph V) (f : W → V) (hf : Function.Injective f) (T : Finset W) :
    ell (G.comap f) T = ell G (T.image f) := by
  let e : (G.comap f).induce (↑T : Set W) ≃g G.induce (↑(T.image f) : Set V) :=
    { toEquiv := (Equiv.Set.image f (↑T : Set W) hf).trans
        (Set.equivOfEq (by exact (Finset.coe_image).symm))
      map_rel_iff' := by intro a b; rfl }
  exact list_iso e

omit [Fintype V] [DecidableEq V] in
lemma ell_mono (G : SimpleGraph V) {S T : Finset V} (h : S⊆T) : ell G S ≤ ell G T :=
  (listChromaticNumber_le_iff _ _).mpr
    (choosable_induce_subset (choosable_listChromaticNumber _) h)

omit [DecidableEq V] in
lemma ell_le (G : SimpleGraph V) (S : Finset V) : ell G S ≤ listChromaticNumber G :=
  (listChromaticNumber_le_iff _ _).mpr (choosable_induce (choosable_listChromaticNumber G) _)

omit [DecidableEq V] in
lemma ell_univ (G : SimpleGraph V) : ell G univ = listChromaticNumber G := by
  let e : G.induce (↑(univ : Finset V) : Set V) ≃g G :=
    { toEquiv := { toFun := Subtype.val
                   invFun := fun v => ⟨v,mem_univ v⟩
                   left_inv := fun _ => rfl
                   right_inv := fun _ => rfl }
      map_rel_iff' := by intro a b; rfl }
  exact list_iso e

omit [Fintype V] in
lemma ell_delete (G : SimpleGraph V) (S Z : Finset V) :
    ell G S ≤ ell G (S\Z) + Z.card := by
  let X : Finset (↑S : Set V) := univ.filter (fun v => v.val∈Z)
  have he : (univ\X).image Subtype.val = S\Z := by
    ext v
    simp only [mem_image,mem_sdiff,mem_univ,mem_filter,true_and,X]
    constructor
    · rintro ⟨w,hw,rfl⟩; exact ⟨w.property,hw⟩
    · rintro ⟨hs,hz⟩; exact ⟨⟨v,hs⟩,hz,rfl⟩
  have hX : X.card ≤ Z.card := by
    rw [←card_image_of_injective X Subtype.val_injective]
    apply card_le_card
    rintro v hv
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
    exact (mem_filter.mp hw).2
  have hh := listChromaticNumber_deleted (G.induce (↑S : Set V)) X
  have ht := ell_image G (Subtype.val : (↑S : Set V) → V) Subtype.val_injective (univ\X)
  rw [he] at ht
  change ell (G.induce (↑S : Set V)) (univ\X) = _ at ht
  change ell G S - X.card ≤ ell (G.induce (↑S : Set V)) (univ\X) at hh
  rw [ht] at hh
  omega

lemma extract_on (G : SimpleGraph V) (S : Finset V) {k : ℕ} (hk : 1≤k)
    (hl : 6*k < ell G S) :
    ∃ T⊆S, KConnectedOn G T k ∧ ell G S ≤ ell G T + 6*k := by
  obtain ⟨T,hTc,hTl⟩ := list_connectivity_extraction (G.induce (↑S:Set V)) hk hl
  refine ⟨T.image Subtype.val,by rintro v hv; obtain ⟨w,hw,rfl⟩ := mem_image.mp hv; exact w.property,
    Knitting.kConnected_image G Subtype.val Subtype.val_injective hTc,?_⟩
  have he := ell_image G (Subtype.val : (↑S : Set V) → V) Subtype.val_injective T
  change ell (G.induce (↑S:Set V)) T = _ at he
  change ell G S - 6*k ≤ ell (G.induce (↑S:Set V)) T at hTl
  rw [he] at hTl
  omega

theorem districts_on : ∀ K : ℕ, 0<K → ∃ D : ℕ,
    max (400*3202) (12800*K)<D ∧ ∃ t₀ : ℕ, ∀ t : ℕ, t₀≤t →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V),
    hadwigerNumber G<t → 2*D*t+2<ell G S →
    ∃ J⊆S, KConnectedOn G J (K*t) ∧ (J.card:ℝ)≤(t:ℝ)^(53/50:ℝ) := by
  intro K hK
  obtain ⟨D,hD,T,hT⟩ := District.list_district K hK
  refine ⟨D,hD,T,?_⟩
  intro t ht V _ _ G S hminor hl
  obtain ⟨J,hJc,hJs⟩ := hT t ht (↑S:Set V) (G.induce (↑S:Set V))
    ((Knitting.model_induce G S).hadwiger_le.trans_lt hminor) hl
  refine ⟨J.image Subtype.val,by rintro v hv; obtain ⟨w,hw,rfl⟩ := mem_image.mp hv; exact w.property,
    Knitting.kConnected_image G Subtype.val Subtype.val_injective hJc,?_⟩
  simpa only [card_image_of_injective _ Subtype.val_injective] using hJs

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open Finset SmallList
attribute [local instance] Classical.propDecidable

theorem small_set_loss_on : ∃ T : ℕ, ∀ t : ℕ, T≤t →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S X : Finset V),
    hadwigerNumber G<t → (X.card:ℝ)≤(t:ℝ)^(53/50:ℝ) →
    ell G S ≤ ell G (S\X)+(4*32768+5)*t ∨ FractionalObstruction G := by
  classical
  obtain ⟨T,hT⟩ := additive_deletion_or_obstruction
  refine ⟨max 1 T,?_⟩
  intro t ht V _ _ G S X hminor hXs
  have ht1 : 1≤t := (le_max_left _ _).trans ht
  let Y : Finset (↑S:Set V) := univ.filter (fun v => v.val∈X)
  have hY : Y.card≤X.card := by
    rw [←card_image_of_injective Y Subtype.val_injective]
    apply card_le_card
    rintro v hv
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
    exact (mem_filter.mp hw).2
  have hsize : (Y.card:ℝ)≤(t:ℝ)^(11/10:ℝ) := by
    apply (by exact_mod_cast hY : (Y.card:ℝ)≤X.card).trans
    apply hXs.trans
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast ht1) (by norm_num)
  have he : (univ\(Y∪∅)).image Subtype.val=S\X := by
    ext v
    simp only [union_empty,mem_image,mem_sdiff,mem_univ,mem_filter,true_and,Y]
    constructor
    · rintro ⟨w,hw,rfl⟩; exact ⟨w.property,hw⟩
    · rintro ⟨hv,hx⟩; exact ⟨⟨v,hv⟩,hx,rfl⟩
  rcases hT t ((le_max_right _ _).trans ht) (↑S:Set V) (G.induce (↑S:Set V)) Y ∅ 0
    ((Knitting.model_induce G S).hadwiger_le.trans_lt hminor) hsize (by simp)
    (by intro A hA hAn; have ha : A=∅ := subset_empty.mp hA; simp [ha] at hAn)
    (by simp) with hl|hb
  · left
    have hz := ell_image G (Subtype.val : (↑S:Set V)→V) Subtype.val_injective (univ\(Y∪∅))
    rw [he] at hz
    change ell (G.induce (↑S:Set V)) (univ\(Y∪∅)) = _ at hz
    change ell G S ≤ ell (G.induce (↑S:Set V)) (univ\(Y∪∅))+(4*32768+0+5)*t at hl
    simpa only [hz,Nat.add_zero] using hl
  · exact Or.inr (obstruction_induce G S hb)

theorem two_districts : ∀ K : ℕ, 0<K → ∃ D : ℕ,
    max (400*3202) (12800*K)<D ∧ ∃ T : ℕ, ∀ t : ℕ, T≤t →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V),
    hadwigerNumber G<t → (2*D+4*32768+5)*t+2<ell G S →
    (∃ J⊆S, ∃ H⊆S, Disjoint J H ∧ KConnectedOn G J (K*t) ∧
      KConnectedOn G H (K*t) ∧ (J.card:ℝ)≤(t:ℝ)^(53/50:ℝ) ∧
      (H.card:ℝ)≤(t:ℝ)^(53/50:ℝ)) ∨ FractionalObstruction G := by
  intro K hK
  obtain ⟨D,hD,T,hT⟩ := districts_on K hK
  obtain ⟨T',hT'⟩ := small_set_loss_on
  refine ⟨D,hD,max T T',?_⟩
  intro t ht V _ _ G S hminor hl
  obtain ⟨J,hJS,hJc,hJsize⟩ := hT t ((le_max_left _ _).trans ht) V G S hminor (by nlinarith)
  rcases hT' t ((le_max_right _ _).trans ht) V G S J hminor hJsize with hloss|hbad
  · obtain ⟨H,hHS,hHc,hHsize⟩ := hT t ((le_max_left _ _).trans ht) V G (S\J) hminor (by nlinarith)
    exact Or.inl ⟨J,hJS,H,hHS.trans sdiff_subset,
      Finset.disjoint_left.mpr (fun v hvJ hvH => (mem_sdiff.mp (hHS hvH)).2 hvJ),hJc,hHc,hJsize,hHsize⟩
  · exact Or.inr hbad

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Footprint
open Finset
attribute [local instance] Classical.propDecidable

structure Round {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (t : ℕ) (F : Finset V) where
  tips : Finset V
  district : Finset V
  junction : Finset V
  roots : Finset V
  first : System G
  second : System G
  tips_subset : tips ⊆ F
  tips_card : tips.card ≤ t
  district_card : (district.card:ℝ) ≤ (t:ℝ)^(106/100:ℝ)
  junction_card : (junction.card:ℝ) ≤ (t:ℝ)^(106/100:ℝ)
  district_disjoint : Disjoint district F
  junction_disjoint : Disjoint junction (F∪district)
  roots_subset : roots ⊆ district
  first_domain : first.domain = univ\(F\tips)
  first_starts : first.starts ⊆ tips∪roots
  tips_start : tips ⊆ first.starts
  first_ends : first.ends ⊆ junction
  first_count : first.n ≤ 4*t
  second_domain : second.domain = univ\(F∪roots)
  second_starts : Disjoint second.starts (F∪district∪junction∪first.used)
  second_injective : Function.Injective second.source
  second_ends : second.ends ⊆ junction
  second_count : second.n ≤ 2*t

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t : ℕ}

noncomputable def Round.final {F : Finset V} (R : Round G t F) : Finset V :=
  F∪R.district∪R.junction∪R.first.used∪R.second.used

namespace History

def initial (W : Finset V) (hW : W.card ≤ t) : History G t where
  q := 0
  footprint := fun _ => W
  initial_card := hW
  tips := Fin.elim0
  district := Fin.elim0
  junction := Fin.elim0
  roots := Fin.elim0
  first := Fin.elim0
  second := Fin.elim0
  tips_subset := by intro i; exact Fin.elim0 i
  tips_card := by intro i; exact Fin.elim0 i
  district_card := by intro i; exact Fin.elim0 i
  junction_card := by intro i; exact Fin.elim0 i
  district_disjoint := by intro i; exact Fin.elim0 i
  junction_disjoint := by intro i; exact Fin.elim0 i
  roots_subset := by intro i; exact Fin.elim0 i
  first_domain := by intro i; exact Fin.elim0 i
  first_starts := by intro i; exact Fin.elim0 i
  tips_start := by intro i; exact Fin.elim0 i
  first_ends := by intro i; exact Fin.elim0 i
  first_count := by intro i; exact Fin.elim0 i
  second_domain := by intro i; exact Fin.elim0 i
  second_starts := by intro i; exact Fin.elim0 i
  second_injective := by intro i; exact Fin.elim0 i
  second_ends := by intro i; exact Fin.elim0 i
  second_count := by intro i; exact Fin.elim0 i
  next := by intro i; exact Fin.elim0 i

noncomputable def append (H : History G t) (R : Round G t (H.footprint H.q)) : History G t where
  q := H.q+1
  footprint j := if j ≤ H.q then H.footprint j else R.final
  initial_card := by simpa using H.initial_card
  tips := Fin.lastCases R.tips H.tips
  district := Fin.lastCases R.district H.district
  junction := Fin.lastCases R.junction H.junction
  roots := Fin.lastCases R.roots H.roots
  first := Fin.lastCases R.first H.first
  second := Fin.lastCases R.second H.second
  tips_subset := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.tips_subset
    · simpa [j.isLt.le] using H.tips_subset j
  tips_card := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.tips_card
    · simpa using H.tips_card j
  district_card := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.district_card
    · simpa using H.district_card j
  junction_card := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.junction_card
    · simpa using H.junction_card j
  district_disjoint := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.district_disjoint
    · simpa [j.isLt.le] using H.district_disjoint j
  junction_disjoint := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.junction_disjoint
    · simpa [j.isLt.le] using H.junction_disjoint j
  roots_subset := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.roots_subset
    · simpa using H.roots_subset j
  first_domain := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.first_domain
    · simpa [j.isLt.le] using H.first_domain j
  first_starts := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.first_starts
    · simpa using H.first_starts j
  tips_start := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.tips_start
    · simpa using H.tips_start j
  first_ends := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.first_ends
    · simpa using H.first_ends j
  first_count := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.first_count
    · simpa using H.first_count j
  second_domain := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.second_domain
    · simpa [j.isLt.le] using H.second_domain j
  second_starts := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.second_starts
    · simpa [j.isLt.le] using H.second_starts j
  second_injective := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.lastCases_last]; exact R.second_injective
    · rw [Fin.lastCases_castSucc]; exact H.second_injective j
  second_ends := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.second_ends
    · simpa using H.second_ends j
  second_count := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.second_count
    · simpa using H.second_count j
  next := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Round.final]
    · simpa [j.isLt.le,Nat.succ_le_iff.mpr j.isLt] using H.next j

lemma append_final (H : History G t) (R : Round G t (H.footprint H.q)) :
    (H.append R).footprint (H.append R).q = R.final := by simp [append]

lemma append_footprint (H : History G t) (R : Round G t (H.footprint H.q))
    (j : ℕ) (hj : j≤H.q) : (H.append R).footprint j=H.footprint j := by simp [append,hj]

end History
end LinearListHadwiger.Footprint

namespace LinearListHadwiger.BagRouting
open Finset SimpleGraph
variable {V I J K : Type} {G : SimpleGraph V} {s : I → V} {B : J → Set V}

def reindex (D : BagRouting G s B) (e : K ≃ I) : BagRouting G (s ∘ e) B where
  paths i := D.paths (e i)
  bag i := D.bag (e i)
  bag_injective := D.bag_injective.comp e.injective
  endpoint_mem i := D.endpoint_mem (e i)
  overlap i j hij := D.overlap (e i) (e j) (fun h => hij (e.injective h))

lemma reindex_totalLength [Fintype I] [Fintype K] (D : BagRouting G s B) (e : K ≃ I) :
    (D.reindex e).totalLength = D.totalLength := by
  exact Equiv.sum_comp e (fun i => (D.paths i).2.val.length)

lemma minimal_reindex [Fintype I] [Fintype K] {D : BagRouting G s B}
    (hD : D.Minimal) (e : K ≃ I) : (D.reindex e).Minimal := by
  intro E
  let F : BagRouting G s B := {
    paths i := ⟨(E.paths (e.symm i)).1,
      ⟨(E.paths (e.symm i)).2.val.copy (by simp) rfl,
        by simpa only [Walk.isPath_copy] using (E.paths (e.symm i)).2.property⟩⟩
    bag i := E.bag (e.symm i)
    bag_injective := E.bag_injective.comp e.symm.injective
    endpoint_mem i := E.endpoint_mem (e.symm i)
    overlap i j hij v hvi hvj := by
      have hh := E.overlap (e.symm i) (e.symm j)
        (fun he => hij (e.symm.injective he)) v
        (by simpa only [Walk.support_copy] using hvi)
        (by simpa only [Walk.support_copy] using hvj)
      simpa using hh }
  rw [reindex_totalLength]
  have hF : F.totalLength = E.totalLength := by
    simpa only [totalLength,F,Walk.length_copy] using
      Equiv.sum_comp e.symm (fun i => (E.paths i).2.val.length)
  exact hF ▸ hD F

lemma minimal_target_only [Fintype I] [DecidableEq I] [DecidableEq V]
    {T : Finset V} {D : BagRouting G s (fun v : ↥T => {v.val})}
    (hD : D.Minimal) (hST : ∀ i, s i ∉ T) (i : I) (v : V)
    (hv : v∈(D.paths i).2.val.support) (hT : v∈T) : v=(D.paths i).1 := by
  classical
  let b : ↥T := ⟨v,hT⟩
  by_cases hb : b∈Set.range D.bag
  · obtain ⟨j,hj⟩ := hb
    have hvj : v=(D.paths j).1 := by
      have hh := D.endpoint_mem j
      simpa only [hj,Set.mem_singleton_iff,b] using hh.symm
    by_cases hij : i=j
    · subst j; exact hvj
    · have hh := D.overlap i j hij v hv (hvj ▸ (D.paths j).2.val.end_mem_support)
      exact (hST i (hh.1 ▸ hT)).elim
  · exact ((not_lt_of_ge (hD (D.truncate i b hb v hv rfl)))
      (D.truncate_length_lt (fun a b hab => Set.disjoint_singleton.mpr
        (fun h => hab (Subtype.ext h))) i b hb v hv rfl)).elim

end LinearListHadwiger.BagRouting

namespace LinearListHadwiger.DoublePacking
variable {V : Type} {G : SimpleGraph V} {A B : Finset V}

def routing (D : DoublePacking G A B) :
    BagRouting G (fun i : ↥A × Bool => i.1.val) (fun b : ↥B => {b.val}) where
  paths i := ⟨(D.target i).val,D.route i⟩
  bag := D.target
  bag_injective := D.target_injective
  endpoint_mem _ := rfl
  overlap := D.overlap

lemma exists_minimal (h : Nonempty (DoublePacking G A B)) :
    ∃ D : BagRouting G (fun i : ↥A × Bool => i.1.val) (fun b : ↥B => {b.val}),
      D.Minimal := by
  obtain ⟨D⟩ := h
  exact BagRouting.exists_minimal ⟨D.routing⟩

end LinearListHadwiger.DoublePacking

end OAI
