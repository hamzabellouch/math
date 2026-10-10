import OAI.Combinatorics.ListHadwiger.Separability

namespace OAI

namespace LinearListHadwiger.Sampling
open Fractional FixedDecomposition
variable {V Ω : Type} [Fintype V] [DecidableEq V] [Fintype Ω]

lemma expectation_inter_card {V Ω : Type} [Fintype V] [DecidableEq V] [Fintype Ω] {μ : Ω → ℝ} (W : Ω → Finset V) (U : Finset V) :
    expectation μ (fun ω => ((W ω ∩ U).card : ℝ)) =
      ∑ v ∈ U, probability μ (fun ω => v ∈ W ω) := by
  classical
  have hc (ω : Ω) : ((W ω ∩ U).card : ℝ) = ∑ v ∈ U, if v ∈ W ω then 1 else 0 := by
    rw [← Finset.sum_filter]
    simp [Finset.filter_mem_eq_inter,Finset.inter_comm]
  simp only [expectation,hc,Finset.mul_sum,probability]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

lemma expectation_inter_card_le {μ : Ω → ℝ} (W : Ω → Finset V) {p : ℝ}
    (hp : ∀ v, probability μ (fun ω => v ∈ W ω) ≤ p) (U : Finset V) :
    expectation μ (fun ω => ((W ω ∩ U).card : ℝ)) ≤ (U.card : ℝ)*p := by
  rw [expectation_inter_card]
  calc
    _ ≤ ∑ _v ∈ U, p := Finset.sum_le_sum (fun v _ => hp v)
    _ = _ := by simp

theorem fixed_region {G : SimpleGraph V} {S : Finset V} {k : ℕ}
    {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (hμsum : ∑ ω, μ ω = 1)
    (W : Ω → Finset V) (hWS : ∀ ω, W ω ⊆ S)
    {r p ε : ℝ} (hr : 0 < r) (hp : 0 ≤ p) (hε : 0 ≤ ε)
    (hsurv : ∀ v, probability μ (fun ω => v ∈ W ω) ≤ p)
    (hsparse : (2*k : ℕ)*p ≤ r/1000)
    (htailCard : ∀ U : Finset V, probability μ (fun ω => r/200 ≤
      |((W ω ∩ U).card : ℝ) - expectation μ (fun z => ((W z ∩ U).card : ℝ))|) ≤ ε)
    (htailFrac : ∀ U : Finset V, probability μ (fun ω => r/20 ≤
      |number (G.induce (↑(W ω ∩ U) : Set V)) -
        expectation μ (fun z => number (G.induce (↑(W z ∩ U) : Set V)))|) ≤ ε)
    (hsmall : ((S.card+1 : ℕ)^2 : ℝ)*ε < 1)
    (hfail : ∀ ω, 0 < μ ω → r/2 < number (G.induce (↑(W ω) : Set V))) :
    ∃ H ⊆ S, KConnectedOn G H k ∧
      r/4 < expectation μ (fun ω => number (G.induce (↑(W ω ∩ H) : Set V))) := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨d,hd⟩ := exists_bounded_tree (G := G) (k := k) S
  let Idx := Fin d.leaves.length ⊕ Fin d.separators.length
  let cardBad (U : Finset V) (ω : Ω) : Prop := r/200 ≤
    |((W ω ∩ U).card : ℝ)-expectation μ (fun z => ((W z ∩ U).card : ℝ))|
  let fracBad (U : Finset V) (ω : Ω) : Prop := r/20 ≤
    |number (G.induce (↑(W ω ∩ U) : Set V))-
      expectation μ (fun z => number (G.induce (↑(W z ∩ U) : Set V)))|
  let bad : Idx → Ω → Prop := fun i => match i with
    | .inl l => if (d.leaves.get l).card ≤ 2*k then cardBad (d.leaves.get l)
      else fracBad (d.leaves.get l)
    | .inr z => cardBad (d.separators.get z)
  have hbad (i : Idx) : probability μ (bad i) ≤ ε := by
    cases i with
    | inl l =>
      dsimp [bad]
      split_ifs
      · exact htailCard _
      · exact htailFrac _
    | inr z => exact htailCard _
  have hcard : Fintype.card Idx ≤ (S.card+1)^2 := by
    simpa [Idx] using hd.trans (budget_le_square k S.card)
  have hcardR : (Fintype.card Idx : ℝ) ≤ ((S.card+1 : ℕ)^2 : ℝ) := by exact_mod_cast hcard
  have hbadall : probability μ (fun ω => ∃ i, bad i ω) < 1 := by
    calc
      _ ≤ ∑ i, probability μ (bad i) := probability_union_le hμ bad
      _ ≤ ∑ _ : Idx, ε := Finset.sum_le_sum (fun i _ => hbad i)
      _ = (Fintype.card Idx : ℝ)*ε := by simp
      _ ≤ ((S.card+1 : ℕ)^2 : ℝ)*ε := mul_le_mul_of_nonneg_right hcardR hε
      _ < 1 := hsmall
  obtain ⟨ω,hω,havoid⟩ := exists_positive_avoiding hμ hμsum hbadall
  have hsmallset (U : Finset V) (hU : U.card ≤ 2*k) (hgood : ¬cardBad U ω) :
      ((W ω ∩ U).card : ℝ) < r/100 := by
    have he := expectation_inter_card_le W hsurv U
    have hUr : (U.card : ℝ) ≤ (2*k : ℕ) := by exact_mod_cast hU
    have hmean : expectation μ (fun z => ((W z ∩ U).card : ℝ)) ≤ r/1000 :=
      he.trans ((mul_le_mul_of_nonneg_right hUr hp).trans hsparse)
    have hdev := (abs_lt.mp (lt_of_not_ge hgood)).2
    linarith
  have hsep : ∀ Z ∈ d.separators, ((W ω ∩ Z).card : ℝ) ≤ r/100 := by
    intro Z hZ
    obtain ⟨z,hz⟩ := List.mem_iff_get.mp hZ
    apply (hsmallset Z (by have := d.separator_small hZ; omega) ?_).le
    have hh : ¬bad (.inr z) ω := fun h => havoid ⟨.inr z,h⟩
    simpa only [bad,hz] using hh
  have hleaf : ∀ L ∈ d.leaves, number (G.induce (↑(W ω ∩ L) : Set V)) ≤ 3*r/10 := by
    intro L hL
    obtain ⟨l,hl⟩ := List.mem_iff_get.mp hL
    have hh : ¬bad (.inl l) ω := fun h => havoid ⟨.inl l,h⟩
    by_cases hs : L.card ≤ 2*k
    · have hc : ¬cardBad L ω := by simpa only [bad,hl,ite_eq_left hs] using hh
      have hc' := hsmallset L hs hc
      have hn : number (G.induce (↑(W ω ∩ L) : Set V)) ≤ ((W ω ∩ L).card : ℝ) := by
        simpa [Finset.filter_mem_eq_inter, Finset.inter_comm] using
          number_le_card (G.induce (↑(W ω ∩ L) : Set V))
      linarith
    · have hf : ¬fracBad L ω := by simpa only [bad,hl,ite_eq_right hs] using hh
      have hconn := (d.leaf_stop hL).resolve_left hs
      have hmean := hn L (d.leaf_subset hL) hconn
      have hdev := (abs_lt.mp (lt_of_not_ge hf)).2
      linarith
  have hnow := fractional_le_leaves_add_separator d (hWS ω)
    (by positivity : (0 : ℝ) ≤ 3*r/10) (by positivity : (0 : ℝ) ≤ r/100) hleaf hsep
  have hf := hfail ω hω
  linarith

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.PairedSources
open SimpleGraph PathPacking
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

def graph (G : SimpleGraph V) (s : I → Bool → V) (U : Set V) : SimpleGraph (I ⊕ V) where
  Adj x y := match x,y with
    | .inl _, .inl _ => False
    | .inl i, .inr v => v ∈ U ∧ (∀ j b, v ≠ s j b) ∧ ∃ b, G.Adj (s i b) v
    | .inr v, .inl i => v ∈ U ∧ (∀ j b, v ≠ s j b) ∧ ∃ b, G.Adj (s i b) v
    | .inr v, .inr w => v ∈ U ∧ w ∈ U ∧ (∀ j b, v ≠ s j b) ∧
        (∀ j b, w ≠ s j b) ∧ G.Adj v w
  symm := ⟨by
    intro x y h
    cases x <;> cases y
    · exact h.elim
    · exact h
    · exact h
    · exact ⟨h.2.1,h.1,h.2.2.2.1,h.2.2.1,h.2.2.2.2.symm⟩⟩
  loopless := ⟨by
    intro x h
    cases x
    · exact h
    · exact h.2.2.2.2.ne rfl⟩

variable {G : SimpleGraph V} {s : I → Bool → V} {U : Set V}

noncomputable def routeHom (i : I) (b : Bool) {v : V}
    (p : G.Path (s i b) v)
    (hU : ∀ w ∈ p.val.support, w ∈ U)
    (hsource : ∀ w ∈ p.val.support, ∀ j c, w = s j c → w = s i b) :
    G.induce {w | w ∈ p.val.support} →g graph G s U where
  toFun w := if w.val = s i b then .inl i else .inr w.val
  map_rel' := by
    intro x y hxy
    change G.Adj x.val y.val at hxy
    dsimp
    split_ifs with hx hy hy
    · exact (hxy.ne (hx.trans hy.symm)).elim
    · exact ⟨hU _ y.property,fun j c he => hy (hsource _ y.property j c he),
        b,by simpa only [hx] using hxy⟩
    · exact ⟨hU _ x.property,fun j c he => hx (hsource _ x.property j c he),
        b,by simpa only [hy] using hxy.symm⟩
    · exact ⟨hU _ x.property,hU _ y.property,
        fun j c he => hx (hsource _ x.property j c he),
        fun j c he => hy (hsource _ y.property j c he),hxy⟩

lemma lift_regular {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I] {G : SimpleGraph V} {s : I → Bool → V} {U : Set V} {x y : I ⊕ V} (q : (graph G s U).Walk x y)
    (h : ∀ i, Sum.inl i ∉ q.support) {u v : V}
    (hx : x = .inr u) (hy : y = .inr v) :
    ∃ p : G.Walk u v, ∀ w ∈ p.support, Sum.inr w ∈ q.support := by
  induction q generalizing u with
  | nil =>
    have huv : u = v := Sum.inr.inj (hx.symm.trans hy)
    subst v
    refine ⟨Walk.nil,?_⟩
    intro w hw
    have : w = u := by simpa using hw
    subst w
    simp [hx]
  | @cons x z y e q ih =>
    have hq : ∀ i, Sum.inl i ∉ q.support := fun i hi => h i (by simp [hi])
    cases z with
    | inl j => exact (hq j q.start_mem_support).elim
    | inr z =>
      obtain ⟨p,hp⟩ := ih hq rfl hy
      have he : G.Adj u z := by
        rw [hx] at e
        exact e.2.2.2.2
      refine ⟨Walk.cons he p,?_⟩
      intro w hw
      simp only [Walk.support_cons,List.mem_cons] at hw ⊢
      rcases hw with rfl | hw
      · exact Or.inl hx.symm
      · exact Or.inr (hp w hw)

structure Packing (G : SimpleGraph V) (s : I → Bool → V) (D : Finset V)
    (U : Set V) where
  choose : I → Bool
  target : I → ↥D
  route : ∀ i, G.Path (s i (choose i)) (target i).val
  disjoint : ∀ i j, i ≠ j → Disjoint {v | v ∈ (route i).val.support}
    {v | v ∈ (route j).val.support}
  source_only : ∀ i v, v ∈ (route i).val.support →
    (∃ j b, v = s j b) → v = s i (choose i)
  target_only : ∀ i v, v ∈ (route i).val.support → v ∈ D → v = (target i).val
  inside : ∀ i v, v ∈ (route i).val.support → v ∈ U

lemma mapped_route {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I] {G : SimpleGraph V} {s : I → Bool → V} {U : Set V} (i : I) (b : Bool) {v : V}
    (p : G.Path (s i b) v)
    (hU : ∀ w ∈ p.val.support, w ∈ U)
    (hsource : ∀ w ∈ p.val.support, ∀ j c, w = s j c → w = s i b)
    (hv : v ≠ s i b) :
    ∃ q : (graph G s U).Walk (.inl i) (.inr v),
      (∀ j, Sum.inl j ∈ q.support → j = i) ∧
      (∀ w, Sum.inr w ∈ q.support → w ∈ p.val.support) := by
  classical
  let f := routeHom i b p hU hsource
  let q0 := (p.val.induce {w | w ∈ p.val.support} (fun _ => id)).map f
  have hs : Sum.inl i = f ⟨s i b,p.val.start_mem_support⟩ := by simp [f,routeHom]
  have ht : Sum.inr v = f ⟨v,p.val.end_mem_support⟩ := by simp [f,routeHom,hv]
  refine ⟨q0.copy hs.symm ht.symm,?_,?_⟩
  · intro j hj
    simp only [Walk.support_copy,q0,Walk.support_map] at hj
    obtain ⟨w,_,hw⟩ := List.mem_map.mp hj
    by_cases h : w.val = s i b
    · have he : Sum.inl i = (Sum.inl j : I ⊕ V) := by
        simpa [f,routeHom,h] using hw
      exact (Sum.inl.inj he).symm
    · have he : Sum.inr w.val = (Sum.inl j : I ⊕ V) := by
        simp [f,routeHom,h] at hw
      cases he
  · intro w hw
    simp only [Walk.support_copy,q0,Walk.support_map] at hw
    obtain ⟨z,_,hz⟩ := List.mem_map.mp hw
    by_cases h : z.val = s i b
    · have he : Sum.inl i = (Sum.inr w : I ⊕ V) := by
        simp [f,routeHom,h] at hz
      cases he
    · have he : Sum.inr z.val = (Sum.inr w : I ⊕ V) := by
        simpa [f,routeHom,h] using hz
      exact (Sum.inr.inj he) ▸ z.property

def Valid (s : I → Bool → V) (U : Set V) : I ⊕ V → Prop
  | .inl _ => True
  | .inr v => v ∈ U ∧ ∀ j b, v ≠ s j b

lemma ordinary_valid_on_walk {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I] {G : SimpleGraph V} {s : I → Bool → V} {U : Set V} {x y : I ⊕ V} (q : (graph G s U).Walk x y)
    (hx : Valid s U x) :
    ∀ v, Sum.inr v ∈ q.support → v ∈ U ∧ ∀ j b, v ≠ s j b := by
  induction q with
  | @nil x =>
    intro v hv
    have hh : Sum.inr v = x := by simpa using hv
    simpa only [← hh,Valid] using hx
  | @cons x z y e q ih =>
    have hz : Valid s U z := by
      cases z with
      | inl _ => trivial
      | inr z =>
        cases x with
        | inl _ => exact ⟨e.1,e.2.1⟩
        | inr _ => exact ⟨e.2.1,e.2.2.2.1⟩
    intro v hv
    simp only [Walk.support_cons,List.mem_cons] at hv
    rcases hv with hv | hv
    · simpa only [← hv,Valid] using hx
    · exact ih hz v hv

lemma lift_source_path {i : I} {v : V}
    (q : (graph G s U).Path (.inl i) (.inr v))
    (hsource : ∀ j, Sum.inl j ∈ q.val.support → j = i) :
    ∃ b : Bool, ∃ p : G.Path (s i b) v,
      ∀ w ∈ p.val.support, w = s i b ∨
        (Sum.inr w ∈ q.val.support ∧ w ∈ U ∧ ∀ j c, w ≠ s j c) := by
  obtain ⟨q,hq⟩ := q
  cases q with
  | @cons _ z _ e q =>
    cases z with
    | inl j => exact e.elim
    | inr z =>
      obtain ⟨hzU,hzs,b,he⟩ := e
      have havoid : ∀ j, Sum.inl j ∉ q.support := by
        intro j hj
        have hji := hsource j (List.mem_cons_of_mem _ hj)
        subst j
        exact ((Walk.cons_isPath_iff _ _).mp hq).2 hj
      obtain ⟨p,hp⟩ := lift_regular q havoid rfl rfl
      let p0 := Walk.cons he p
      refine ⟨b,p0.toPath,?_⟩
      intro w hw
      have hww := p0.support_toPath_subset_support hw
      simp only [p0,Walk.support_cons,List.mem_cons] at hww
      rcases hww with hww | hww
      · exact Or.inl hww
      · have hqmem : Sum.inr w ∈ (Walk.cons (show (graph G s U).Adj (.inl i) (.inr z) from
            ⟨hzU,hzs,b,he⟩) q).support := by simp [hp w hww]
        exact Or.inr ⟨hqmem,ordinary_valid_on_walk
          (Walk.cons (show (graph G s U).Adj (.inl i) (.inr z) from
            ⟨hzU,hzs,b,he⟩) q) (show Valid s U (.inl i) from trivial) w hqmem⟩

theorem combine {D : Finset V} (target : I → Bool → ↥D)
    (route : ∀ i b, G.Path (s i b) (target i b).val)
    (hgroups : ∀ i b j c, s i b = s j c → i = j)
    (hD : ∀ v ∈ D, ∀ i b, v ≠ s i b)
    (hU : ∀ i b v, v ∈ (route i b).val.support → v ∈ U)
    (hS : ∀ i b v, v ∈ (route i b).val.support →
      ∀ j c, v = s j c → v = s i b)
    (hcon : ∀ v, (Finset.univ.filter (fun ib : I × Bool =>
      v ∈ (route ib.1 ib.2).val.support)).card ≤ 2) :
    Nonempty (Packing G s D U) := by
  classical
  let Q := graph G s U
  let A : Finset (I ⊕ V) := Finset.univ.map ⟨Sum.inl,Sum.inl_injective⟩
  let B : Finset (I ⊕ V) := D.map ⟨Sum.inr,Sum.inr_injective⟩
  have hq (ib : I × Bool) := mapped_route ib.1 ib.2 (route ib.1 ib.2)
    (hU ib.1 ib.2) (hS ib.1 ib.2)
    (hD _ (target ib.1 ib.2).property ib.1 ib.2)
  choose q hqL hqR using hq
  have hconQ (x : I ⊕ V) :
      (Finset.univ.filter (fun ib : I × Bool => x ∈ (q ib).support)).card ≤ 2 := by
    cases x with
    | inl i =>
      have hsub : (Finset.univ.filter (fun ib : I × Bool => Sum.inl i ∈ (q ib).support)) ⊆
          ({i} ×ˢ (Finset.univ : Finset Bool)) := by
        intro ib hib
        have he : ib.1 = i := (hqL ib i (Finset.mem_filter.mp hib).2).symm
        exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr he,Finset.mem_univ _⟩
      simpa using Finset.card_le_card hsub
    | inr v =>
      apply (Finset.card_le_card ?_).trans (hcon v)
      intro ib hib
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hqR ib v (Finset.mem_filter.mp hib).2⟩
  have hAC : A.card = Fintype.card I := by simp [A]
  have hPI : 2*A.card ≤ Fintype.card (I × Bool) := by simp [hAC,Fintype.card_prod]; omega
  have hpack : Nonempty (FullPacking Q A B) := by
    apply fullPacking_of_no_small_separator
    intro X hX
    obtain ⟨ib,hi⟩ := exists_region_avoiding (fun ib => {x | x ∈ (q ib).support})
      X 2 A.card (by omega) hPI hX (fun x _ => hconQ x)
    exact ⟨Sum.inl ib.1,by simp [A],Sum.inr (target ib.1 ib.2).val,
      by simp [B,(target ib.1 ib.2).property],q ib,hi⟩
  obtain ⟨P⟩ := hpack
  let a (i : I) : ↥A := ⟨.inl i,by simp [A]⟩
  have ha : Function.Injective a := by
    intro i j hij
    exact Sum.inl.inj (congrArg Subtype.val hij)
  have hd (i : I) : ∃ d : ↥D, (P.target (a i)).val = Sum.inr d.val := by
    obtain ⟨v,hv,hve⟩ := Finset.mem_map.mp (P.target (a i)).property
    exact ⟨⟨v,hv⟩,hve.symm⟩
  choose dest hdest using hd
  let qp (i : I) : Q.Path (.inl i) (.inr (dest i).val) :=
    ⟨(P.route (a i)).val.copy rfl (hdest i),by
      simpa only [Walk.isPath_copy] using (P.route (a i)).property⟩
  have hqps (i j : I) (h : Sum.inl j ∈ (qp i).val.support) : j = i := by
    have hh := P.source_only (a i) (Sum.inl j) (by simpa [qp] using h) (by simp [A])
    exact Sum.inl.inj hh
  have hlift (i : I) := lift_source_path (qp i) (hqps i)
  choose b p hp using hlift
  refine ⟨⟨b,dest,p,?_,?_,?_,?_⟩⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro w hwi hwj
    rcases hp i w hwi with hi | hi <;> rcases hp j w hwj with hj | hj
    · exact hij (hgroups i (b i) j (b j) (hi.symm.trans hj))
    · exact hj.2.2 i (b i) hi
    · exact hi.2.2 j (b j) hj
    · exact Set.disjoint_left.mp (P.disjoint (a i) (a j) (fun h => hij (ha h)))
        (by simpa [qp] using hi.1) (by simpa [qp] using hj.1)
  · intro i v hv ⟨j,c,hvS⟩
    rcases hp i v hv with h | h
    · exact h
    · exact (h.2.2 j c hvS).elim
  · intro i v hv hvD
    rcases hp i v hv with h | h
    · exact (hD v hvD i (b i) h).elim
    · have hh := P.target_only (a i) (Sum.inr v) (by simpa [qp] using h.1)
        (by simp [B,hvD])
      rw [hdest i] at hh
      exact Sum.inr.inj hh
  · intro i v hv
    rcases hp i v hv with h | h
    · simpa only [h] using hU i (b i) _ (route i (b i)).val.start_mem_support
    · exact h.2.1

end LinearListHadwiger.PairedSources

end OAI
