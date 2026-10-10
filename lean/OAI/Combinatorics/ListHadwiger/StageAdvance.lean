import OAI.Combinatorics.ListHadwiger.BagAssembly

namespace OAI

namespace LinearListHadwiger.Stage
open Finset SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma woven_induce (G : SimpleGraph V) (J : Finset V) {a b : ℕ}
    (hw : Woven (G.induce (↑J : Set V)) a b) : WovenOn G (↑J : Set V) a b := by
  classical
  intro roots hr hJ p hp x y hxy he
  let r' (i : Fin a) : (↑J : Set V) := ⟨roots i,hJ i⟩
  let x' (i : Fin p) : (↑J : Set V) := ⟨x i,(hxy i).1⟩
  let y' (i : Fin p) : (↑J : Set V) := ⟨y i,(hxy i).2⟩
  have he' : ∀ i j, i≠j → Disjoint ({x' i,y' i} : Set (↑J:Set V)) {x' j,y' j} := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro v hv hw
    apply Set.disjoint_left.mp (he i j hij) (show v.val∈({x i,y i}:Set V) from ?_)
      (show v.val∈({x j,y j}:Set V) from ?_)
    · simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,Subtype.ext_iff,x',y'] using hv
    · simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,Subtype.ext_iff,x',y'] using hw
  obtain ⟨A⟩ := hw r' (fun i j hij => hr (congrArg Subtype.val hij)) (by simp)
    p hp x' y' (by simp) he'
  let N := Knitting.model_induce G J
  let M : RootedCliqueModel G roots := {
    branch := fun i => N.expand (A.model.branch i)
    connected := fun i => N.expand_connected (A.model.connected i)
    disjoint := fun i j hij => N.expand_disjoint (A.model.disjoint i j hij)
    adjacent := by
      intro i j hij
      obtain ⟨v,hv,w,hw,hvw⟩ := A.model.adjacent i j hij
      exact ⟨v.val,⟨v,hv,rfl⟩,w.val,⟨w,hw,rfl⟩,hvw⟩
    root_mem := fun i => ⟨r' i,A.model.root_mem i,rfl⟩ }
  let f : (G.induce (↑J:Set V)) →g G := ⟨Subtype.val,fun h => h⟩
  let paths : ∀ i, G.Path (x i) (y i) := fun i =>
    ⟨(A.paths i).val.map f,(A.paths i).property.map Subtype.val_injective⟩
  have hpath (i : Fin p) (v : V) : v∈(paths i).val.support ↔
      ∃ w : (↑J:Set V), w∈(A.paths i).val.support ∧ w.val=v := by
    simp only [paths,Walk.support_map,List.mem_map]
    rfl
  have hbranch (i : Fin a) (v : V) : v∈M.branch i ↔
      ∃ w : (↑J:Set V), w∈A.model.branch i ∧ w.val=v := by
    simp only [M,N,MinorModel.expand,Knitting.model_induce,Set.mem_ofPred_eq,Set.mem_singleton_iff]
    constructor
    · rintro ⟨w,hw,h⟩; exact ⟨w,hw,h.symm⟩
    · rintro ⟨w,hw,h⟩; exact ⟨w,hw,h.symm⟩
  refine ⟨⟨M,?_,paths,?_,?_,?_⟩⟩
  · intro i v hv
    obtain ⟨w,hw,rfl⟩ := (hbranch i v).mp hv
    exact w.property
  · intro i v hv
    obtain ⟨w,hw,rfl⟩ := (hpath i v).mp hv
    exact w.property
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro v hv hw
    obtain ⟨w,hw',rfl⟩ := (hpath i v).mp hv
    obtain ⟨z,hz,heq⟩ := (hpath j w.val).mp hw
    exact Set.disjoint_left.mp (A.disjoint i j hij) hw'
      (show w∈(A.paths j).val.support from (Subtype.ext heq : z=w) ▸ hz)
  · intro i j v hv hb
    obtain ⟨w,hw,rfl⟩ := (hpath i v).mp hv
    obtain ⟨z,hz,heq⟩ := (hbranch j w.val).mp hb
    have hz' : w∈A.model.branch j := (Subtype.ext heq : z=w) ▸ hz
    obtain ⟨⟨k,hk⟩,hend⟩ := A.clean i j w hw hz'
    refine ⟨⟨k,congrArg Subtype.val hk⟩,?_⟩
    exact hend.imp (congrArg Subtype.val) (congrArg Subtype.val)

theorem districts_woven : ∃ T : ℕ, ∀ t : ℕ, T≤t → ∀ s : ℕ,
    1 ≤ s → s ≤ 2*⌈(t:ℝ)/(Real.log t)^2⌉₊ →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (J : Finset V),
    (J.card:ℝ)≤(t:ℝ)^(53/50:ℝ) → KConnectedOn G J ((100000*65536)*t) →
    WovenOn G (↑J:Set V) s (3*t) := by
  classical
  obtain ⟨T,hT⟩ := Assembly.small_districts_woven
  refine ⟨T,?_⟩
  intro t ht s hs hst V _ _ G J hJs hJc
  apply woven_induce
  exact hT t ht s hs hst (↑J:Set V) (G.induce (↑J:Set V))
    (by rw [show Fintype.card (↑J:Set V)=J.card from Fintype.card_coe J]; exact hJs) (Knitting.induce_connected G J hJc)

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open Finset Footprint SmallList
attribute [local instance] Classical.propDecidable

abbrev K₀ : ℕ := 100000*65536
abbrev cf : ℕ := 4*32768+6*3202+25
abbrev ch : ℕ := cf+6*(K₀+1)+2

def Inseparable {V : Type} [DecidableEq V] (G : SimpleGraph V) (r b : ℕ) : Prop :=
  ∀ A B : Finset V, Disjoint A B → r ≤ ell G A+b → r ≤ ell G B+b → False

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
lemma choose_vertices {S : Finset V} {n : ℕ} (h : n≤S.card) :
    ∃ w : Fin n → V, Function.Injective w ∧ ∀ i, w i∈S := by
  obtain ⟨T,hTS,hT⟩ := Finset.exists_subset_card_eq h
  let e : Fin n ≃ ↥T := (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hT)).symm
  exact ⟨fun i => (e i).val,Subtype.val_injective.comp e.injective,fun i => hTS (e i).property⟩

omit [Fintype V] in
lemma overlap_of_inseparable {r b a c k : ℕ} {H H' : Finset V}
    (hn : Inseparable G r b) (hH : r≤ell G H+a) (hH' : r≤ell G H'+c)
    (ha : a≤b) (hc : c+k≤b) : k≤(H∩H').card := by
  by_contra hh
  have hcard : (H'∩H).card<k := by simpa only [inter_comm] using Nat.lt_of_not_ge hh
  have hl := ell_delete G H' (H'∩H)
  apply hn H (H'\(H'∩H)) (Finset.disjoint_left.mpr (by
    intro v hv hw
    exact (mem_sdiff.mp hw).2 (mem_inter.mpr ⟨(mem_sdiff.mp hw).1,hv⟩)))
  · omega
  · omega

lemma restore_region {t r : ℕ} (ht : 0<t) (H' F T : Finset V)
    (hc : KConnectedOn G H' ((K₀+1)*t))
    (hl : r≤ell G H'+(cf+6*(K₀+1))*t)
    (hHF : H'∩F=T) (hT : T.card=2*t)
    (w : Fin t → V) (hw : Function.Injective w) (hwT : ∀ i, w i∈T) :
    let W := univ.image w
    let H := H'\(T\W)
    KConnectedOn G H (K₀*t) ∧ r≤ell G H+ch*t ∧ H∩F=W := by
  let W := univ.image w
  have hW : W.card=t := by simp only [W,card_image_of_injective _ hw,card_univ,Fintype.card_fin]
  have hWT : W⊆T := by rintro v hv; obtain ⟨i,hi,rfl⟩ := mem_image.mp hv; exact hwT i
  have hTH : T⊆H' := by rw [←hHF]; exact inter_subset_left
  have hdel : (T\W).card=t := by have hh := card_sdiff_add_card_eq_card hWT; omega
  have hdt : (T\W).card<(K₀+1)*t := by rw [hdel]; dsimp [K₀]; omega
  have hconn := Knitting.delete_connected G hc (sdiff_subset.trans hTH) hdt
  have hlev : (K₀+1)*t-(T\W).card=K₀*t := by rw [hdel,Nat.add_mul,one_mul,Nat.add_sub_cancel]
  rw [hlev] at hconn
  refine ⟨hconn,?_,?_⟩
  · have hh := ell_delete G H' (T\W)
    rw [hdel] at hh
    change r≤ell G (H'\(T\W))+ch*t
    dsimp [ch,cf,K₀] at hl ⊢
    omega
  · ext v
    simp only [mem_inter,mem_sdiff]
    constructor
    · rintro ⟨⟨hv,hnot⟩,hf⟩
      have hvT : v∈T := hHF ▸ mem_inter.mpr ⟨hv,hf⟩
      by_contra hw
      exact hnot ⟨hvT,hw⟩
    · intro hw
      have hvT := hWT hw
      have hvHF : v∈H'∩F := hHF.symm ▸ hvT
      exact ⟨⟨(mem_inter.mp hvHF).1,fun hh => hh.2 hw⟩,(mem_inter.mp hvHF).2⟩

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open Finset Footprint SmallList
attribute [local instance] Classical.propDecidable

structure State {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (t r : ℕ) where
  history : History G t
  bag : Fin t → Set V
  tip : Fin t → V
  connected : ∀ i, (G.induce (bag i)).Connected
  disjoint : ∀ i j, i≠j → Disjoint (bag i) (bag j)
  inside : ∀ i, bag i⊆(↑(history.footprint history.q) : Set V)
  tip_mem : ∀ i, tip i∈bag i
  tip_injective : Function.Injective tip
  region : Finset V
  region_conn : KConnectedOn G region (K₀*t)
  region_list : r≤ell G region+ch*t
  intersection : region∩history.footprint history.q=univ.image tip

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t r : ℕ}

namespace State
lemma tip_region (A : State G t r) (i : Fin t) : A.tip i∈A.region := by
  have hh : A.tip i∈A.region∩A.history.footprint A.history.q := by rw [A.intersection]; simp
  exact (mem_inter.mp hh).1

lemma tip_footprint (A : State G t r) (i : Fin t) : A.tip i∈A.history.footprint A.history.q :=
  A.inside i (A.tip_mem i)

lemma live_disjoint (A : State G t r) :
    Disjoint (A.region\univ.image A.tip) (A.history.footprint A.history.q) := by
  apply Finset.disjoint_left.mpr
  intro v hv hf
  exact (mem_sdiff.mp hv).2 (A.intersection ▸ mem_inter.mpr ⟨(mem_sdiff.mp hv).1,hf⟩)

theorem initial (ht : 0<t) (hr : 6*(K₀*t)<listChromaticNumber G) :
    ∃ A : State G t (listChromaticNumber G), A.history.q=0 := by
  obtain ⟨H,hHU,hHc,hHl⟩ := extract_on G univ (by dsimp [K₀]; omega : 1≤K₀*t)
    (by simpa only [ell_univ] using hr)
  obtain ⟨w,hw,hwH⟩ := choose_vertices (show t≤H.card from by have hh := hHc.1; dsimp [K₀] at hh; omega)
  let W := univ.image w
  have hW : W.card≤t := by simp only [W,card_image_of_injective _ hw,card_univ,Fintype.card_fin,le_refl]
  let A : State G t (listChromaticNumber G) := {
    history := History.initial W hW
    bag := fun i => {w i}
    tip := w
    connected := fun i => SimpleGraph.Connected.of_subsingleton
    disjoint := fun i j hij => Set.disjoint_singleton.mpr (fun he => hij (hw he))
    inside := by intro i v hv; have he : v=w i := hv; simp [History.initial,W,he]
    tip_mem := fun _ => rfl
    tip_injective := hw
    region := H
    region_conn := hHc
    region_list := by
      rw [ell_univ] at hHl
      dsimp [ch,cf,K₀] at hHl ⊢
      omega
    intersection := by
      change H∩W=W
      exact inter_eq_right.mpr (by rintro v hv; obtain ⟨i,hi,rfl⟩ := mem_image.mp hv; exact hwH i) }
  exact ⟨A,rfl⟩
end State

noncomputable def firstRound (A : State G t r) (J D : Finset V)
    (hJ : (J.card:ℝ)≤(t:ℝ)^(53/50:ℝ)) (hD : (D.card:ℝ)≤(t:ℝ)^(53/50:ℝ))
    (hJF : Disjoint J (A.history.footprint A.history.q))
    (hDFJ : Disjoint D (A.history.footprint A.history.q∪J))
    {a : ℕ} (u : Fin a → V) (huJ : ∀ j, u j∈J)
    (R : System G) (hRU : R.domain=univ\(A.history.footprint A.history.q\univ.image A.tip))
    (hRS : R.starts=oldSources A.tip u) (hRE : R.ends⊆D) (hRn : R.n≤4*t) :
    Round G t (A.history.footprint A.history.q) where
  tips := univ.image A.tip
  district := J
  junction := D
  roots := univ.image u
  first := R
  second := System.empty (univ\(A.history.footprint A.history.q∪univ.image u))
  tips_subset := by rintro v hv; obtain ⟨i,hi,rfl⟩ := mem_image.mp hv; exact A.tip_footprint i
  tips_card := by simp only [card_image_of_injective _ A.tip_injective,card_univ,Fintype.card_fin,le_refl]
  district_card := by simpa only [show (106/100:ℝ)=53/50 by norm_num] using hJ
  junction_card := by simpa only [show (106/100:ℝ)=53/50 by norm_num] using hD
  district_disjoint := hJF
  junction_disjoint := hDFJ
  roots_subset := by rintro v hv; obtain ⟨i,hi,rfl⟩ := mem_image.mp hv; exact huJ i
  first_domain := hRU
  first_starts := by rw [hRS]; exact subset_refl _
  tips_start := by rw [hRS]; exact subset_union_left
  first_ends := hRE
  first_count := hRn
  second_domain := rfl
  second_starts := by simp
  second_injective := by intro i; exact Fin.elim0 i
  second_ends := by simp
  second_count := Nat.zero_le _

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open Finset Footprint SmallList
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t r : ℕ}

theorem second_system (A : State G t r) (ht : 0<t) (J D H' : Finset V)
    (hJH : J⊆A.region) (hDS : D⊆A.region\univ.image A.tip)
    (hJD : Disjoint J D) (hDc : KConnectedOn G D (K₀*t))
    {a : ℕ} (u : Fin a → V) (hua : a≤t) (huJ : ∀ j, u j∈J)
    (hHp : KConnectedOn G H' ((K₀+1)*t))
    (hHpFJ : Disjoint H' (A.history.footprint A.history.q∪J))
    (hover : K₀*t≤(A.region∩H').card) :
    Nonempty (Second G (univ\(A.history.footprint A.history.q∪univ.image u)) H' D (2*t)) := by
  let Z := oldSources A.tip u
  have hZ : Z.card≤2*t := by
    have h1 : (univ.image A.tip).card≤t := by simpa using card_image_le (s:=univ) (f:=A.tip)
    have h2 : (univ.image u).card≤a := by simpa using card_image_le (s:=univ) (f:=u)
    have hh := card_union_le (univ.image A.tip) (univ.image u)
    dsimp [Z,oldSources]
    omega
  have hZH : Z⊆A.region := by
    intro v hv
    rcases (mem_oldSources _ _ v).mp hv with ⟨i,rfl⟩|⟨j,rfl⟩
    · exact A.tip_region i
    · exact hJH (huJ j)
  have hZH' : Disjoint Z H' := by
    apply Finset.disjoint_left.mpr
    intro v hv hvP
    rcases (mem_oldSources _ _ v).mp hv with ⟨i,rfl⟩|⟨j,rfl⟩
    · exact Finset.disjoint_left.mp hHpFJ hvP (mem_union_left _ (A.tip_footprint i))
    · exact Finset.disjoint_left.mp hHpFJ hvP (mem_union_right _ (huJ j))
  have hZD : Disjoint Z D := by
    apply Finset.disjoint_left.mpr
    intro v hv hvD
    rcases (mem_oldSources _ _ v).mp hv with ⟨i,rfl⟩|⟨j,rfl⟩
    · exact (mem_sdiff.mp (hDS hvD)).2 (by simp)
    · exact Finset.disjoint_left.mp hJD (huJ j) hvD
  have hconn := union_connected G A.region_conn
    (Knitting.kConnected_mono hHp (by dsimp [K₀]; omega)) hover
  have hz : Z.card<K₀*t := by dsimp [K₀]; omega
  have hconn' := Knitting.delete_connected G hconn (hZH.trans subset_union_left) hz
  have hlevel : 2*t≤K₀*t-Z.card := by dsimp [K₀]; omega
  apply Second.exists_in_region _ ((A.region∪H')\Z) _ _ _ ?_ ?_ ?_
    (Knitting.kConnected_mono hconn' hlevel)
    (by have hh := hHp.1; dsimp [K₀] at hh; omega)
    (by have hh := hDc.1; dsimp [K₀] at hh; omega)
  · intro v hv
    obtain ⟨hv,hz⟩ := mem_sdiff.mp hv
    refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
    intro hf
    rcases mem_union.mp hf with hf|hu
    · rcases mem_union.mp hv with hvH|hvP
      · have hw : v∈univ.image A.tip := A.intersection ▸ mem_inter.mpr ⟨hvH,hf⟩
        exact hz (mem_union_left _ hw)
      · exact Finset.disjoint_left.mp hHpFJ hvP (mem_union_left _ hf)
    · exact hz (mem_union_right _ hu)
  · intro v hv
    exact mem_sdiff.mpr ⟨mem_union_right _ hv,fun hz => Finset.disjoint_left.mp hZH' hz hv⟩
  · intro v hv
    exact mem_sdiff.mpr ⟨mem_union_left _ (mem_sdiff.mp (hDS hv)).1,
      fun hz => Finset.disjoint_left.mp hZD hz hv⟩

noncomputable def completeRound {F H : Finset V} (R : Round G t F)
    (Q : Second G (univ\(F∪R.roots)) H R.junction (2*t))
    (hH : Disjoint H (F∪R.district∪R.junction∪R.first.used)) : Round G t F :=
  { R with
    second := Q.record
    second_domain := Q.record_domain
    second_starts := by
      apply hH.mono_left
      intro v hv
      rw [Q.record_starts] at hv
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
      exact Q.source_mem i
    second_injective := Q.record_source_injective
    second_ends := Q.record_ends
    second_count := (Q.record_count).le }

lemma completeRound_intersection {F H : Finset V} (R : Round G t F)
    (Q : Second G (univ\(F∪R.roots)) H R.junction (2*t))
    (hH : Disjoint H (F∪R.district∪R.junction∪R.first.used)) :
    H∩(completeRound R Q hH).final=Q.record.starts := by
  rw [←Q.used_inter_region]
  ext v
  simp only [completeRound,Round.final,mem_inter,mem_union]
  constructor
  · rintro ⟨hv,hf|hq⟩
    · exact False.elim (Finset.disjoint_left.mp hH hv (by simpa only [mem_union] using hf))
    · exact ⟨hq,hv⟩
  · rintro ⟨hq,hv⟩; exact ⟨hv,Or.inr hq⟩

end LinearListHadwiger.Stage

end OAI
