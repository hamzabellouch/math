import OAI.Combinatorics.VariableWL.GeneralGame

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10

namespace VariableWL.Blocks
attribute [local instance] Classical.propDecidable
open VariableWL.Affine
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} (J : ProductImages.Instance r P E) (marked : Fin r)

noncomputable def completeList (U : Finset (Block (n := n) J))
    (ξ : ∀ b : ↑U, Valuation J marked 1 b.val) : ∀ b : Block (n := n) J, Valuation J marked 1 b := by
  classical
  exact fun b => if h : b ∈ U then ξ ⟨b,h⟩ else
    ⟨Classical.choose (legal_nonempty J marked 1 b.val),Classical.choose_spec (legal_nonempty J marked 1 b.val)⟩

theorem completeList_mem (U : Finset (Block (n := n) J))
    (ξ : ∀ b : ↑U, Valuation J marked 1 b.val) (b : ↑U) :
    completeList J marked U ξ b.val = ξ b := by
  classical
  simp [completeList,b.property]

def GlobalPool (hr : 3 ≤ r) (hn : 0 < n) (Q : J.Witness)
    (U : Finset (Block (n := n) J)) : Set (∀ b : Block (n := n) J, Valuation J marked 1 b) :=
  {ξ | (fun b : ↑U => ξ b.val) ∈ OffsetLists J hr hn marked Q U}

theorem globalPool_nonempty (hr : 3 ≤ r) (hn : 0 < n) (hlarge : r+1 < n+1)
    (Q : J.Witness) (U : Finset (Block (n := n) J)) (hU : U.card ≤ r+1) :
    (GlobalPool J marked hr hn Q U).Nonempty := by
  obtain ⟨ξ,hξ⟩ := offsetLists_nonempty J hr hn hlarge marked Q U hU
  refine ⟨completeList J marked U ξ,?_⟩
  change (fun b : ↑U => completeList J marked U ξ b.val) ∈ OffsetLists J hr hn marked Q U
  simpa only [completeList_mem] using hξ

theorem globalPool_down (hr : 3 ≤ r) (hn : 0 < n) (hlarge : r+1 < n+1)
    (Q : J.Witness) (U V : Finset (Block (n := n) J)) (hU : U.card ≤ r+1) (hVU : V ⊆ U) :
    GlobalPool J marked hr hn Q U ⊆ GlobalPool J marked hr hn Q V := by
  intro ξ hξ
  change (fun b : ↑V => ξ b.val) ∈ OffsetLists J hr hn marked Q V
  rw [← exact_projection J hr hn hlarge marked Q U V hU hVU]
  exact ⟨fun b : ↑U => ξ b.val,hξ,rfl⟩

theorem globalPool_extend (hr : 3 ≤ r) (hn : 0 < n) (hlarge : r+1 < n+1)
    (Q : J.Witness) (U : Finset (Block (n := n) J)) (hU : U.card < r+1)
    (b : Block (n := n) J) (ξ : ∀ c : Block (n := n) J, Valuation J marked 1 c)
    (hξ : ξ ∈ GlobalPool J marked hr hn Q U) :
    ∃ η ∈ GlobalPool J marked hr hn Q (insert b U), ∀ c ∈ U, η c = ξ c := by
  classical
  have hsize : (insert b U).card ≤ r+1 := Finset.card_insert_le _ _ |>.trans (by omega)
  have hsub : U ⊆ insert b U := Finset.subset_insert _ _
  rw [GlobalPool,Set.mem_ofPred_eq,← exact_projection J hr hn hlarge marked Q (insert b U) U hsize hsub] at hξ
  obtain ⟨η,hη,he⟩ := hξ
  refine ⟨completeList J marked (insert b U) η,?_,?_⟩
  · change (fun c : ↑(insert b U) => completeList J marked (insert b U) η c.val) ∈ OffsetLists J hr hn marked Q (insert b U)
    simpa only [completeList_mem] using hη
  · intro c hc
    exact (completeList_mem J marked (insert b U) η ⟨c,hsub hc⟩).trans (congrFun he ⟨c,hc⟩)
end VariableWL.Blocks

namespace VariableWL.General
open Blocks VariableWL.Affine
variable {r n : ℕ} {P : Type uVariable3} {E : Type uVariable4} [Fintype P] [Fintype E]
variable (J : ProductImages.Instance r P E) (marked : Fin r)

noncomputable def numberedTranslation (ξ : ∀ b : Block (n := n) J, Valuation J marked 1 b) :
    Fin (finiteGraph J marked (n := n) 0).order ≃ Fin (finiteGraph J marked (n := n) 1).order :=
  (Fintype.equivFin _).symm.trans ((vertexEquiv J marked (leafCount J marked) ξ).trans (Fintype.equivFin _))

noncomputable def numberedPart (v : Fin (finiteGraph J marked (n := n) 0).order) : Block (n := n) J :=
  ((Fintype.equivFin (Vertex J marked (leafCount J marked) 0)).symm v).1

theorem numberedTranslation_local
    (ξ η : ∀ b : Block (n := n) J, Valuation J marked 1 b)
    (v : Fin (finiteGraph J marked (n := n) 0).order)
    (h : ξ (numberedPart J marked v) = η (numberedPart J marked v)) :
    numberedTranslation J marked ξ v = numberedTranslation J marked η v := by
  let x := (Fintype.equivFin (Vertex J marked (leafCount J marked) 0)).symm v
  have hh : ξ x.1 = η x.1 := h
  change (Fintype.equivFin (Vertex J marked (leafCount J marked) 1)) (vertexEquiv J marked (leafCount J marked) ξ x) =
    (Fintype.equivFin (Vertex J marked (leafCount J marked) 1)) (vertexEquiv J marked (leafCount J marked) η x)
  apply congrArg
  change (⟨x.1, (translateValuation J marked x.1 (ξ x.1)) x.2.1, x.2.2⟩ : Vertex J marked (leafCount J marked) 1) =
    ⟨x.1, (translateValuation J marked x.1 (η x.1)) x.2.1, x.2.2⟩
  rw [hh]

theorem winning_of_witness (hr : 3 ≤ r) (hn : 0 < n) (hlarge : r+1 < n+1)
    (Q : J.Witness) :
    Game.Winning (fun _ : Fin (r+1) => none :
      Game.Position (finiteGraph J marked (n := n) 0) (finiteGraph J marked (n := n) 1) (r+1)) := by
  classical
  apply Game.winning_of_block_families (numberedPart J marked)
    (numberedTranslation J marked) (numberedTranslation_local J marked)
    (GlobalPool J marked hr hn Q)
  · exact globalPool_nonempty J marked hr hn hlarge Q ∅ (by simp)
  · exact globalPool_down J marked hr hn hlarge Q
  · exact globalPool_extend J marked hr hn hlarge Q
  · intro U ξ hξ v w hv hw
    let x := (Fintype.equivFin (Vertex J marked (leafCount J marked) 0)).symm v
    let y := (Fintype.equivFin (Vertex J marked (leafCount J marked) 0)).symm w
    have hag : Agree J marked ⟨x.1,ξ x.1⟩ ⟨y.1,ξ y.1⟩ := by
      intro a ha hb
      exact offsetLists_agree J hr hn marked Q U hξ ⟨x.1,hv⟩ ⟨y.1,hw⟩ a ha hb
    have hh := (adjacency_translate J marked (by omega) hn (leafCount J marked) ξ x y hag).symm
    change (graph J marked (leafCount J marked) 0).Adj x y ↔
      (graph J marked (leafCount J marked) 1).Adj
        ((Fintype.equivFin (Vertex J marked (leafCount J marked) 1)).symm
          ((Fintype.equivFin (Vertex J marked (leafCount J marked) 1)) (vertexEquiv J marked (leafCount J marked) ξ x)))
        ((Fintype.equivFin (Vertex J marked (leafCount J marked) 1)).symm
          ((Fintype.equivFin (Vertex J marked (leafCount J marked) 1)) (vertexEquiv J marked (leafCount J marked) ξ y)))
    simpa only [Equiv.symm_apply_apply] using hh
end VariableWL.General

namespace VariableWL.General
open Blocks VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable5} {E : Type uVariable6} [Fintype P] [Fintype E]
variable (J : ProductImages.Instance r P E) (marked : Fin r)

theorem base_card_equal :
    Fintype.card (Base (n := n) J marked 0) = Fintype.card (Base (n := n) J marked 1) := by
  classical
  let ξ : ∀ b : Block (n := n) J, Valuation J marked 1 b := fun b =>
    ⟨Classical.choose (legal_nonempty J marked 1 b.val),Classical.choose_spec (legal_nonempty J marked 1 b.val)⟩
  exact Fintype.card_congr (baseEquiv J marked ξ)

theorem base_neighbors_lt {ε : Bit} (v : Base (n := n) J marked ε) :
    Fintype.card {w : Base (n := n) J marked ε // BaseAdj J marked v w} <
      Fintype.card (Base (n := n) J marked ε) :=
  Fintype.card_subtype_lt (x := v) (fun hv => hv.1 rfl)

theorem base_degree_quotient {ε : Bit}
    (hc : Fintype.card (Base (n := n) J marked ε) = Fintype.card (Base (n := n) J marked 0))
    (v : Base (n := n) J marked ε) :
    (graph J marked (leafCount J marked) ε).degree (baseVertex J marked (leafCount J marked) v) /
      (Fintype.card (Base (n := n) J marked 0) + 1) =
        (Fintype.equivFin (Block (n := n) J) v.1).val + 1 := by
  rw [base_degree,leafCount,Nat.add_mul_div_right _ _ (by omega)]
  have hlt := base_neighbors_lt J marked v
  rw [hc] at hlt
  rw [Nat.div_eq_of_lt (by omega : Fintype.card {w : Base (n := n) J marked ε // BaseAdj J marked v w} <
    Fintype.card (Base (n := n) J marked 0) + 1),zero_add]

theorem base_degree_gt_one {ε : Bit}
    (hc : Fintype.card (Base (n := n) J marked ε) = Fintype.card (Base (n := n) J marked 0))
    (v : Base (n := n) J marked ε) :
    1 < (graph J marked (leafCount J marked) ε).degree (baseVertex J marked (leafCount J marked) v) := by
  have hp : 0 < Fintype.card (Base (n := n) J marked ε) := Fintype.card_pos_iff.mpr ⟨v⟩
  rw [hc] at hp
  rw [base_degree,leafCount]
  have hm : Fintype.card (Base (n := n) J marked 0) + 1 ≤
      ((Fintype.equivFin (Block (n := n) J) v.1).val + 1) * (Fintype.card (Base (n := n) J marked 0) + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  omega

noncomputable def numberedIso (ε : Bit) :
    graph J marked (leafCount (n := n) J marked) ε ≃g (finiteGraph J marked (n := n) ε).graph where
  toEquiv := Fintype.equivFin _
  map_rel_iff' := by
    intro v w
    change (graph J marked (leafCount J marked) ε).Adj
      ((Fintype.equivFin (Vertex J marked (leafCount J marked) ε)).symm ((Fintype.equivFin (Vertex J marked (leafCount J marked) ε)) v))
      ((Fintype.equivFin (Vertex J marked (leafCount J marked) ε)).symm ((Fintype.equivFin (Vertex J marked (leafCount J marked) ε)) w)) ↔ _
    rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]

theorem recognized_base {q : ℕ} (hq : 2 ≤ q)
    {p : Game.Position (finiteGraph J marked (n := n) 0) (finiteGraph J marked (n := n) 1) q}
    (hp : Game.Winning p) {i : Fin q} (v : Base (n := n) J marked 0)
    {w : Fin (finiteGraph J marked (n := n) 1).order}
    (hi : p i = some (numberedIso J marked 0 (baseVertex J marked (leafCount J marked) v),w)) :
    ∃ z : Valuation J marked 1 v.1,
      w = numberedIso J marked 1 (baseVertex J marked (leafCount J marked) ⟨v.1,z⟩) := by
  let y := (numberedIso J marked 1).symm w
  have hy : numberedIso J marked 1 y = w := (numberedIso J marked 1).apply_symm_apply w
  have hd := hp.degree_eq hq hi
  rw [(numberedIso J marked 0).degree_eq,← hy,(numberedIso J marked 1).degree_eq] at hd
  have hybase : IsBase J marked y := by
    by_contra hn
    obtain ⟨j,hj⟩ := exists_leaf_of_owner J marked (leafCount J marked) hn rfl
    rw [← hj,leaf_degree] at hd
    have hgt := base_degree_gt_one J marked rfl v
    omega
  have hyn := baseVertex_owner J marked (leafCount J marked) hybase
  have hq0 := base_degree_quotient J marked rfl v
  have hq1 := base_degree_quotient J marked (base_card_equal J marked).symm (owner J marked y)
  rw [hyn,← hd] at hq1
  have hb : (owner J marked y).1 = v.1 := by
    apply (Fintype.equivFin (Block (n := n) J)).injective
    apply Fin.ext
    omega
  obtain ⟨b,z,t⟩ := y
  change t = none at hybase
  subst t
  change b = v.1 at hb
  subst b
  exact ⟨z,hy.symm⟩

noncomputable def zeroQuery (b : Block (n := n) J) : Fin (finiteGraph J marked (n := n) 0).order :=
  numberedIso J marked 0 (baseVertex J marked (leafCount J marked) ⟨b,0,legal_zero J marked b.val⟩)

noncomputable def valuationQuery (b : Block (n := n) J) (z : Valuation J marked 1 b) :
    Fin (finiteGraph J marked (n := n) 1).order :=
  numberedIso J marked 1 (baseVertex J marked (leafCount J marked) ⟨b,z⟩)

theorem zeroQuery_injective : Function.Injective (zeroQuery (n := n) J marked) := by
  intro b c h
  have he := baseVertex_injective J marked (leafCount J marked) ((numberedIso J marked 0).injective h)
  exact congrArg Sigma.fst he

theorem zeroQuery_recognized {q : ℕ} (hq : 2 ≤ q)
    {p : Game.Position (finiteGraph J marked (n := n) 0) (finiteGraph J marked (n := n) 1) q}
    (hp : Game.Winning p) {i : Fin q} {b : Block (n := n) J}
    {w : Fin (finiteGraph J marked (n := n) 1).order} (hi : p i = some (zeroQuery J marked b,w)) :
    ∃ z : Valuation J marked 1 b, w = valuationQuery J marked b z :=
  recognized_base J marked hq hp ⟨b,0,legal_zero J marked b.val⟩ hi

theorem zeroQuery_agree (hr : 3 ≤ r) (hn : 0 < n) {q : ℕ}
    {p : Game.Position (finiteGraph J marked (n := n) 0) (finiteGraph J marked (n := n) 1) q}
    (hp : Game.Winning p) {i j : Fin q} {b c : Block (n := n) J}
    {z : Valuation J marked 1 b} {w : Valuation J marked 1 c}
    (hi : p i = some (zeroQuery J marked b,valuationQuery J marked b z))
    (hj : p j = some (zeroQuery J marked c,valuationQuery J marked c w)) :
    Agree J marked ⟨b,z⟩ ⟨c,w⟩ := by
  intro a hb hc
  by_cases he : b = c
  · subst c
    have heq := (hp.partialIso i j _ _ hi hj).1.mp rfl
    have hz : z = w := by
      have hbase := baseVertex_injective J marked (leafCount J marked) ((numberedIso J marked 1).injective heq)
      exact eq_of_heq (Sigma.mk.inj_iff.mp hbase).2
    exact congrArg (fun t : Valuation J marked 1 b => readout J t.val hb) hz
  · have hadj : (finiteGraph J marked (n := n) 0).graph.Adj (zeroQuery J marked b) (zeroQuery J marked c) := by
      apply (numberedIso J marked 0).map_adj_iff.mpr
      refine Or.inl ⟨rfl,rfl,he,⟨a,hb,hc⟩,?_⟩
      intro d hbd hcd
      change HasReadout J b.val d at hbd
      change HasReadout J c.val d at hcd
      change readout J (0 : RawValue J b.val) hbd = readout J (0 : RawValue J c.val) hcd
      rw [readout_zero J (by omega) hn,readout_zero J (by omega) hn]
    have hresp := (hp.partialIso i j _ _ hi hj).2.mp hadj
    have hraw := (numberedIso J marked 1).map_adj_iff.mp hresp
    rcases hraw with ⟨_,_,h⟩ | ⟨_,h,_⟩ | ⟨h,_,_⟩
    · exact h.2.2 a hb hc
    · exact False.elim (h rfl)
    · exact False.elim (h rfl)
end VariableWL.General

namespace VariableWL.Game
variable {G H : Graph} {r : ℕ} {B : Type uVariable7} {Z : B → Type uVariable9}
variable (query : B → Fin G.order) (response : (Σ b, Z b) → Fin H.order)

def Ring (v : Fin r → Σ b, Z b) : Prop :=
  ∃ p : Position G H (r+1), Winning p ∧
    ∃ σ : Fin r → Fin (r+1), Function.Injective σ ∧
      ∀ i, p (σ i) = some (query (v i).1,response (v i))

variable
  (recognize : ∀ (p : Position G H (r+1)), Winning p → ∀ i b w,
    p i = some (query b,w) → ∃ z : Z b, w = response ⟨b,z⟩)
  (rel : (Σ b, Z b) → (Σ b, Z b) → Prop)
  (agree : ∀ (p : Position G H (r+1)), Winning p → ∀ i j v w,
    p i = some (query v.1,response v) → p j = some (query w.1,response w) → rel v w)

include recognize in
theorem ring_nonempty
    (hwin : Winning (fun _ : Fin (r+1) => none : Position G H (r+1))) (b : Fin r → B) :
    ∃ z : ∀ i, Z (b i), Ring query response (fun i => ⟨b i,z i⟩) := by
  obtain ⟨E,hE⟩ := hwin.fill r Fin.castSucc (Fin.castSucc_injective r) (fun _ => rfl)
  obtain ⟨p,hp,_,hreal⟩ := hE (fun i => query (b i))
  have hz := fun i => recognize p hp (Fin.castSucc i) (b i) (E (fun j => query (b j)) i) (hreal i)
  choose z hz using hz
  refine ⟨z,p,hp,Fin.castSucc,Fin.castSucc_injective r,?_⟩
  intro i
  simpa only [hz i] using hreal i

include agree in
theorem Ring.compatible {v : Fin r → Σ b, Z b} (hv : Ring query response v) (i j : Fin r) :
    rel (v i) (v j) := by
  obtain ⟨p,hp,σ,_,hσ⟩ := hv
  exact agree p hp (σ i) (σ j) (v i) (v j) (hσ i) (hσ j)

include recognize agree in

theorem Ring.replace {v : Fin r → Σ b, Z b} (hv : Ring query response v)
    (i : Fin r) (b : B) :
    ∃ z : Z b, Ring query response (Function.update v i ⟨b,z⟩) ∧
      ∀ j, rel (v j) ⟨b,z⟩ := by
  classical
  obtain ⟨p,hp,σ,hσ,hreal⟩ := hv
  obtain ⟨fresh,hfresh⟩ := exists_fresh σ
  let p0 := Function.update p fresh none
  have hp0 : Winning p0 := hp.discard (clear_subposition p fresh)
  have hreal0 (j : Fin r) : p0 (σ j) = some (query (v j).1,response (v j)) := by
    simpa only [p0,Function.update_of_ne (hfresh j)] using hreal j
  obtain ⟨e,he⟩ := hp0.move fresh (by simp [p0])
  let p1 := Function.update p0 fresh (some (query b,e (query b)))
  have hp1 : Winning p1 := he (query b)
  obtain ⟨z,hz⟩ := recognize p1 hp1 fresh b (e (query b)) (by simp [p1])
  have hnew : p1 fresh = some (query b,response ⟨b,z⟩) := by simp [p1,hz]
  have hold (j : Fin r) : p1 (σ j) = some (query (v j).1,response (v j)) := by
    simpa only [p1,Function.update_of_ne (hfresh j)] using hreal0 j
  refine ⟨z,⟨p1,hp1,Function.update σ i fresh,update_injective_of_fresh hσ i fresh hfresh,?_⟩,
    fun j => agree p1 hp1 (σ j) fresh (v j) ⟨b,z⟩ (hold j) hnew⟩
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [Function.update_self] using hnew
  · simpa only [Function.update_of_ne hj] using hold j

include recognize agree in

theorem Ring.replace_all {v : Fin r → Σ b, Z b} (hv : Ring query response v) (b : Fin r → B) :
    ∃ w : Fin r → Σ b, Z b, Ring query response w ∧
      ∀ i, (w i).1 = b i ∧ rel (v i) (w i) := by
  classical
  have aux (s : Finset (Fin r)) : ∃ w : Fin r → Σ b, Z b, Ring query response w ∧
      (∀ i ∈ s, (w i).1 = b i ∧ rel (v i) (w i)) ∧ ∀ i ∉ s, w i = v i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨v,hv,by simp,fun _ _ => rfl⟩
    | @insert i s hi ih =>
      obtain ⟨w,hw,hinside,houtside⟩ := ih
      obtain ⟨z,hz,hrel⟩ := hw.replace query response recognize rel agree i (b i)
      refine ⟨Function.update w i ⟨b i,z⟩,hz,?_,?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          simpa only [Function.update_self,houtside i hi] using And.intro (rfl : (⟨b i,z⟩ : Σ b, Z b).1 = b i) (hrel i)
        · by_cases hji : j = i
          · subst j; exact False.elim (hi hj)
          · simpa only [Function.update_of_ne hji] using hinside j hj
      · intro j hj
        have hji : j ≠ i := fun h => hj (h ▸ Finset.mem_insert_self _ _)
        rw [Function.update_of_ne hji]
        exact houtside j (fun h => hj (Finset.mem_insert_of_mem h))
  obtain ⟨w,hw,hs,_⟩ := aux Finset.univ
  exact ⟨w,hw,fun i => hs i (Finset.mem_univ _)⟩
end VariableWL.Game

namespace VariableWL.Game
variable {G H : Graph} {r : ℕ} {B : Type uVariable8} {Z Y : B → Type uVariable10}
variable (query : B → Fin G.order) (response : (Σ b, Z b) → Fin H.order)
variable (decode : ∀ b, Z b → Y b)

theorem sigma_eq_cast (s : Σ b, Y b) {b : B} (h : s.1 = b) : s = ⟨b,h ▸ s.2⟩ := by
  cases s
  cases h
  rfl

def decodeSigma (z : Σ b, Z b) : Σ b, Y b := ⟨z.1,decode z.1 z.2⟩

def RingLists (b : Fin r → B) : Set (∀ i, Y (b i)) :=
  {y | ∃ v : Fin r → Σ b, Z b, Ring query response v ∧
    ∀ i, decodeSigma decode (v i) = ⟨b i,y i⟩}

variable
  (recognize : ∀ (p : Position G H (r+1)), Winning p → ∀ i b w,
    p i = some (query b,w) → ∃ z : Z b, w = response ⟨b,z⟩)
  (rel : (Σ b, Y b) → (Σ b, Y b) → Prop)
  (agree : ∀ (p : Position G H (r+1)), Winning p → ∀ i j v w,
    p i = some (query v.1,response v) → p j = some (query w.1,response w) →
      rel (decodeSigma decode v) (decodeSigma decode w))

include recognize in
theorem ringLists_nonempty
    (hwin : Winning (fun _ : Fin (r+1) => none : Position G H (r+1))) (b : Fin r → B) :
    (RingLists query response decode b).Nonempty := by
  obtain ⟨z,hz⟩ := ring_nonempty query response recognize hwin b
  exact ⟨fun i => decode (b i) (z i),fun i => ⟨b i,z i⟩,hz,fun _ => rfl⟩

include agree in
theorem ringLists_compatible {b : Fin r → B} {y : ∀ i, Y (b i)}
    (hy : y ∈ RingLists query response decode b) (i j : Fin r) :
    rel ⟨b i,y i⟩ ⟨b j,y j⟩ := by
  obtain ⟨v,hv,he⟩ := hy
  have h := hv.compatible query response
    (fun v w => rel (decodeSigma decode v) (decodeSigma decode w)) agree i j
  simpa only [he] using h

include recognize agree in
theorem ringLists_transfer {b : Fin r → B} {y : ∀ i, Y (b i)}
    (hy : y ∈ RingLists query response decode b) (c : Fin r → B) :
    ∃ z ∈ RingLists query response decode c, ∀ i, rel ⟨b i,y i⟩ ⟨c i,z i⟩ := by
  obtain ⟨v,hv,hvY⟩ := hy
  obtain ⟨w,hw,hwc⟩ := hv.replace_all query response recognize
    (fun v w => rel (decodeSigma decode v) (decodeSigma decode w)) agree c
  let z : ∀ i, Y (c i) := fun i => (hwc i).1 ▸ decode (w i).1 (w i).2
  have he (i : Fin r) : decodeSigma decode (w i) = ⟨c i,z i⟩ :=
    sigma_eq_cast (decodeSigma decode (w i)) (hwc i).1
  refine ⟨z,⟨w,hw,he⟩,?_⟩
  intro i
  simpa only [hvY i,he i] using (hwc i).2
end VariableWL.Game

end OAI
