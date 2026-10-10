import OAI.Combinatorics.VariableWL.ExactProjection

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL.General
open Blocks VariableWL.Affine
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} (J : ProductImages.Instance r P E)
variable (marked : Fin r)

abbrev Base (ε : Bit) := Σ b : Block (n := n) J, Valuation J marked ε b
abbrev Part (leaves : Block (n := n) J → ℕ) (ε : Bit) (b : Block (n := n) J) :=
  Valuation J marked ε b × Option (Fin (leaves b))
abbrev Vertex (leaves : Block (n := n) J → ℕ) (ε : Bit) :=
  Σ b : Block (n := n) J, Part J marked leaves ε b

def owner {leaves : Block (n := n) J → ℕ} {ε : Bit} (v : Vertex J marked leaves ε) : Base (n := n) J marked ε :=
  ⟨v.1,v.2.1⟩

def IsBase {leaves : Block (n := n) J → ℕ} {ε : Bit} (v : Vertex J marked leaves ε) : Prop :=
  v.2.2 = none

def Shared (b c : Block (n := n) J) : Prop :=
  ∃ a : Readout r n P E, HasReadout J b.val a ∧ HasReadout J c.val a

def Agree {ε ε' : Bit} (v : Base (n := n) J marked ε) (w : Base (n := n) J marked ε') : Prop :=
  ∀ a (hv : HasReadout J v.1.val a) (hw : HasReadout J w.1.val a),
    readout J v.2.val hv = readout J w.2.val hw

def BaseAdj {ε : Bit} (v w : Base (n := n) J marked ε) : Prop :=
  v.1 ≠ w.1 ∧ Shared J v.1 w.1 ∧ Agree J marked v w

theorem baseAdj_symm {ε : Bit} {v w : Base (n := n) J marked ε} (h : BaseAdj J marked v w) :
    BaseAdj J marked w v :=
  ⟨h.1.symm, by obtain ⟨a,hv,hw⟩ := h.2.1; exact ⟨a,hw,hv⟩,
    fun a hw hv => (h.2.2 a hv hw).symm⟩

def graph (leaves : Block (n := n) J → ℕ) (ε : Bit) : SimpleGraph (Vertex J marked leaves ε) where
  Adj v w := (IsBase J marked v ∧ IsBase J marked w ∧ BaseAdj J marked (owner J marked v) (owner J marked w)) ∨
    (IsBase J marked v ∧ ¬ IsBase J marked w ∧ owner J marked v = owner J marked w) ∨
    (¬ IsBase J marked v ∧ IsBase J marked w ∧ owner J marked v = owner J marked w)
  symm := ⟨by
    intro v w h
    rcases h with ⟨hv,hw,h⟩ | ⟨hv,hw,h⟩ | ⟨hv,hw,h⟩
    · exact Or.inl ⟨hw,hv,baseAdj_symm J marked h⟩
    · exact Or.inr (Or.inr ⟨hw,hv,h.symm⟩)
    · exact Or.inr (Or.inl ⟨hw,hv,h.symm⟩)⟩
  loopless := ⟨by
    intro v h
    rcases h with ⟨_,_,h⟩ | ⟨hv,hw,_⟩ | ⟨hv,hw,_⟩
    · exact h.1 rfl
    · exact hw hv
    · exact hv hw⟩

def partEquiv (leaves : Block (n := n) J → ℕ) (b : Block (n := n) J)
    (ξ : Valuation J marked 1 b) : Part J marked leaves 0 b ≃ Part J marked leaves 1 b :=
  (translateValuation J marked b ξ).prodCongr (Equiv.refl _)

def baseEquiv (ξ : ∀ b : Block (n := n) J, Valuation J marked 1 b) :
    Base (n := n) J marked 0 ≃ Base (n := n) J marked 1 :=
  Equiv.sigmaCongrRight (fun b => translateValuation J marked b (ξ b))

def vertexEquiv (leaves : Block (n := n) J → ℕ)
    (ξ : ∀ b : Block (n := n) J, Valuation J marked 1 b) :
    Vertex J marked leaves 0 ≃ Vertex J marked leaves 1 :=
  Equiv.sigmaCongrRight (fun b => partEquiv J marked leaves b (ξ b))

theorem owner_vertexEquiv (leaves : Block (n := n) J → ℕ)
    (ξ : ∀ b : Block (n := n) J, Valuation J marked 1 b) (v : Vertex J marked leaves 0) :
    owner J marked (vertexEquiv J marked leaves ξ v) = baseEquiv J marked ξ (owner J marked v) := rfl

theorem baseAdj_translate (hr : 2 ≤ r) (hn : 0 < n)
    (ξ : ∀ b : Block (n := n) J, Valuation J marked 1 b) (v w : Base (n := n) J marked 0)
    (hξ : Agree J marked ⟨v.1,ξ v.1⟩ ⟨w.1,ξ w.1⟩) :
    BaseAdj J marked (baseEquiv J marked ξ v) (baseEquiv J marked ξ w) ↔ BaseAdj J marked v w := by
  have hread : Agree J marked (baseEquiv J marked ξ v) (baseEquiv J marked ξ w) ↔ Agree J marked v w := by
    constructor <;> intro h a hv hw
    · change HasReadout J v.1.val a at hv
      change HasReadout J w.1.val a at hw
      have ha := h a hv hw
      change readout J (v.2.val + (ξ v.1).val) hv = readout J (w.2.val + (ξ w.1).val) hw at ha
      rw [readout_add J hr hn,readout_add J hr hn,hξ a hv hw] at ha
      exact add_right_cancel ha
    · change HasReadout J v.1.val a at hv
      change HasReadout J w.1.val a at hw
      change readout J (v.2.val + (ξ v.1).val) hv = readout J (w.2.val + (ξ w.1).val) hw
      rw [readout_add J hr hn,readout_add J hr hn,hξ a hv hw,h a hv hw]
  exact and_congr_right (fun _ => and_congr_right (fun _ => hread))

theorem adjacency_translate (hr : 2 ≤ r) (hn : 0 < n)
    (leaves : Block (n := n) J → ℕ) (ξ : ∀ b : Block (n := n) J, Valuation J marked 1 b)
    (v w : Vertex J marked leaves 0)
    (hξ : Agree J marked ⟨v.1,ξ v.1⟩ ⟨w.1,ξ w.1⟩) :
    (graph J marked leaves 1).Adj (vertexEquiv J marked leaves ξ v) (vertexEquiv J marked leaves ξ w) ↔
      (graph J marked leaves 0).Adj v w := by
  change (_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _) ↔
    (_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _)
  have hb (x : Vertex J marked leaves 0) :
      IsBase J marked (vertexEquiv J marked leaves ξ x) ↔ IsBase J marked x := Iff.rfl
  simp only [hb,owner_vertexEquiv,(baseEquiv J marked ξ).injective.eq_iff,
    baseAdj_translate J marked hr hn ξ (owner J marked v) (owner J marked w) hξ]

noncomputable def leafCount [Fintype P] [Fintype E] (b : Block (n := n) J) : ℕ :=
  ((Fintype.equivFin (Block (n := n) J) b).val + 1) * (Fintype.card (Base (n := n) J marked 0) + 1)

noncomputable def finiteGraph [Fintype P] [Fintype E] (ε : Bit) : Graph where
  order := Fintype.card (Vertex J marked (leafCount (n := n) J marked) ε)
  graph := {
    Adj := fun v w => (graph J marked (leafCount (n := n) J marked) ε).Adj
      ((Fintype.equivFin _).symm v) ((Fintype.equivFin _).symm w)
    symm := ⟨fun _ _ h => (graph J marked (leafCount (n := n) J marked) ε).symm.symm _ _ h⟩
    loopless := ⟨fun _ => (graph J marked (leafCount (n := n) J marked) ε).loopless.irrefl _⟩ }

theorem equal_orders [Fintype P] [Fintype E] :
    (finiteGraph J marked (n := n) 0).order = (finiteGraph J marked (n := n) 1).order := by
  classical
  have h (b : Block (n := n) J) : Nonempty (Valuation J marked 1 b) :=
    let ⟨z,hz⟩ := legal_nonempty J marked 1 b.val; ⟨⟨z,hz⟩⟩
  exact Fintype.card_congr (vertexEquiv J marked (leafCount (n := n) J marked) (fun b => Classical.choice (h b)))
end VariableWL.General

namespace VariableWL.Game
attribute [local instance] Classical.propDecidable

theorem winning_reached {G H : Graph} {q : ℕ} (S : Strategy G H q)
    (hS : StrategyWins S) {history : List (Action G H q)} (hh : Reached S history) :
    Winning (historyPosition history) := by
  let A : Set (Position G H q) := {p | ∃ h, Reached S h ∧ historyPosition h = p}
  refine ⟨A, ⟨history,hh,rfl⟩, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro p ⟨h, hh, rfl⟩
    exact (hS h hh).1
  · rintro p ⟨h, hh, rfl⟩ p' hp'
    exact ⟨.discard p' :: h, .discard hh hp', rfl⟩
  · rintro p ⟨h, hh, rfl⟩ i hi
    obtain ⟨e, he⟩ := (hS h hh).2 i hi
    exact ⟨e, fun v => ⟨.place i e v :: h, .place hh hi he, rfl⟩⟩

theorem Winning.neighborhood_bijection {G H : Graph} {q : ℕ} (hq : 2 ≤ q)
    {p : Position G H q} (hp : Winning p) {i : Fin q}
    {a : Fin G.order} {b : Fin H.order} (hi : p i = some (a,b)) :
    ∃ e : Fin G.order ≃ Fin H.order, ∀ v, G.graph.Adj a v ↔ H.graph.Adj b (e v) := by
  classical
  let : Nontrivial (Fin q) := Fin.nontrivial_iff_two_le.mpr hq
  obtain ⟨j,hj⟩ := exists_ne i
  let one : Position G H q := Function.update (fun _ => none) i (some (a,b))
  have hs : Subposition one p := by
    intro l c hc
    by_cases hl : l = i
    · subst l
      have hc' : (a,b) = c := by simpa [one] using hc
      simpa only [← hc'] using hi
    · simp [one,Function.update_of_ne hl] at hc
  have hone := hp.discard hs
  obtain ⟨e,he⟩ := hone.move j (by simp [one,Function.update_of_ne hj])
  refine ⟨e,fun v => ?_⟩
  exact ((he v).partialIso i j (a,b) (v,e v)
    (by simp [Function.update_of_ne hj.symm,one]) (by simp)).2

theorem Winning.degree_eq {G H : Graph} {q : ℕ} (hq : 2 ≤ q)
    {p : Position G H q} (hp : Winning p) {i : Fin q}
    {a : Fin G.order} {b : Fin H.order} (hi : p i = some (a,b)) :
    G.graph.degree a = H.graph.degree b := by
  classical
  obtain ⟨e,he⟩ := hp.neighborhood_bijection hq hi
  let f : G.graph.neighborSet a ≃ H.graph.neighborSet b := {
    toFun := fun v => ⟨e v.val, (he v.val).mp v.property⟩
    invFun := fun w => ⟨e.symm w.val, (he (e.symm w.val)).mpr (by simpa only [Equiv.apply_symm_apply,SimpleGraph.mem_neighborSet] using w.property)⟩
    left_inv := fun v => Subtype.ext (e.symm_apply_apply v.val)
    right_inv := fun w => Subtype.ext (e.apply_symm_apply w.val) }
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using Fintype.card_congr f
end VariableWL.Game

namespace VariableWL.General
open Blocks VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable3} {E : Type uVariable4} (J : ProductImages.Instance r P E) (marked : Fin r)
variable (leaves : Block (n := n) J → ℕ) {ε : Bit}

def baseVertex (v : Base (n := n) J marked ε) : Vertex J marked leaves ε := ⟨v.1,v.2,none⟩
def leafVertex (v : Base (n := n) J marked ε) (i : Fin (leaves v.1)) : Vertex J marked leaves ε :=
  ⟨v.1,v.2,some i⟩

def splitVertex : Vertex J marked leaves ε ≃ Σ v : Base (n := n) J marked ε, Option (Fin (leaves v.1)) where
  toFun v := ⟨⟨v.1,v.2.1⟩,v.2.2⟩
  invFun v := ⟨v.1.1,v.1.2,v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem baseVertex_owner {v : Vertex J marked leaves ε} (hv : IsBase J marked v) :
    baseVertex J marked leaves (owner J marked v) = v := by
  obtain ⟨b,z,t⟩ := v
  change t = none at hv
  subst t
  rfl

theorem leafVertex_injective (v : Base (n := n) J marked ε) :
    Function.Injective (leafVertex J marked leaves v) := by
  intro i j h
  have hVal : (v.2,some i) = (v.2,some j) := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  exact Option.some.inj (congrArg Prod.snd hVal)

theorem baseVertex_injective : Function.Injective (baseVertex J marked leaves (ε := ε)) := by
  intro v w h
  exact congrArg (owner J marked) h

theorem exists_leaf_of_owner {v : Base (n := n) J marked ε} {w : Vertex J marked leaves ε}
    (hw : ¬ IsBase J marked w) (he : owner J marked w = v) :
    ∃ i, leafVertex J marked leaves v i = w := by
  obtain ⟨b,z,t⟩ := w
  change t ≠ none at hw
  obtain ⟨i,rfl⟩ := Option.ne_none_iff_exists'.mp hw
  subst v
  exact ⟨i,rfl⟩

theorem leaf_adj_iff (v : Base (n := n) J marked ε) (i : Fin (leaves v.1))
    (w : Vertex J marked leaves ε) :
    (graph J marked leaves ε).Adj (leafVertex J marked leaves v i) w ↔ w = baseVertex J marked leaves v := by
  constructor
  · intro h
    have hh : IsBase J marked w ∧ v = owner J marked w := by
      rcases h with ⟨hn,_,_⟩ | ⟨hn,_,_⟩ | ⟨_,hb,he⟩
      · simp [IsBase,leafVertex] at hn
      · simp [IsBase,leafVertex] at hn
      · exact ⟨hb,he⟩
    exact ((baseVertex_owner J marked leaves hh.1).symm).trans (congrArg (baseVertex J marked leaves) hh.2.symm)
  · rintro rfl
    exact Or.inr (Or.inr ⟨by simp [IsBase,leafVertex],rfl,rfl⟩)

theorem leaf_degree [Fintype P] [Fintype E] (v : Base (n := n) J marked ε) (i : Fin (leaves v.1)) :
    (graph J marked leaves ε).degree (leafVertex J marked leaves v i) = 1 := by
  classical
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
  exact ⟨baseVertex J marked leaves v,(leaf_adj_iff J marked leaves v i _).mpr rfl,
    fun w hw => (leaf_adj_iff J marked leaves v i w).mp hw⟩

noncomputable def baseNeighbors (v : Base (n := n) J marked ε) :
    {w : Base (n := n) J marked ε // BaseAdj J marked v w} ⊕ Fin (leaves v.1) ≃
      (graph J marked leaves ε).neighborSet (baseVertex J marked leaves v) := by
  let f : {w : Base (n := n) J marked ε // BaseAdj J marked v w} ⊕ Fin (leaves v.1) →
      (graph J marked leaves ε).neighborSet (baseVertex J marked leaves v) := fun x =>
    match x with
    | .inl w => ⟨baseVertex J marked leaves w.val, Or.inl ⟨rfl,rfl,w.property⟩⟩
    | .inr i => ⟨leafVertex J marked leaves v i, Or.inr (Or.inl ⟨rfl,by simp [IsBase,leafVertex],rfl⟩)⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    have hv := congrArg Subtype.val h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subtype.ext (baseVertex_injective J marked leaves hv))
      | inr y =>
        have hbase := congrArg (fun w => IsBase J marked w) hv
        simp [f,baseVertex,leafVertex,IsBase] at hbase
    | inr x =>
      cases y with
      | inl y =>
        have hbase := congrArg (fun w => IsBase J marked w) hv
        simp [f,baseVertex,leafVertex,IsBase] at hbase
      | inr y => exact congrArg Sum.inr (leafVertex_injective J marked leaves v hv)
  · rintro ⟨w,hw⟩
    change (IsBase J marked (baseVertex J marked leaves v) ∧ IsBase J marked w ∧ _) ∨
      (IsBase J marked (baseVertex J marked leaves v) ∧ ¬ IsBase J marked w ∧ _) ∨
      (¬ IsBase J marked (baseVertex J marked leaves v) ∧ IsBase J marked w ∧ _) at hw
    rcases hw with ⟨_,hbase,hadj⟩ | ⟨_,hbase,he⟩ | ⟨hbase,_,_⟩
    · exact ⟨.inl ⟨owner J marked w,hadj⟩,Subtype.ext (baseVertex_owner J marked leaves hbase)⟩
    · obtain ⟨i,hi⟩ := exists_leaf_of_owner J marked leaves hbase he.symm
      exact ⟨.inr i,Subtype.ext hi⟩
    · exact False.elim (hbase rfl)

theorem base_degree [Fintype P] [Fintype E] (v : Base (n := n) J marked ε) :
    (graph J marked leaves ε).degree (baseVertex J marked leaves v) =
      Fintype.card {w : Base (n := n) J marked ε // BaseAdj J marked v w} + leaves v.1 := by
  classical
  simpa only [Fintype.card_sum,Fintype.card_fin,SimpleGraph.card_neighborSet_eq_degree] using
    (Fintype.card_congr (baseNeighbors J marked leaves v)).symm
end VariableWL.General

namespace VariableWL.Game
variable {G H : Graph} {q : ℕ} {B : Type uVariable5} [DecidableEq B]

def active (part : Fin G.order → B) (p : Position G H q) : Finset B :=
  (Finset.univ.image (fun i => (p i).map (fun a => part a.1))).eraseNone

theorem mem_active (part : Fin G.order → B) (p : Position G H q) (b : B) :
    b ∈ active part p ↔ ∃ i a, p i = some a ∧ part a.1 = b := by
  simp only [active,Finset.mem_eraseNone,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi⟩
    obtain ⟨a,ha,he⟩ := Option.map_eq_some_iff.mp hi
    exact ⟨i,a,ha,he⟩
  · rintro ⟨i,a,ha,he⟩
    exact ⟨i,by simp [ha,he]⟩

theorem active_card_le (part : Fin G.order → B) (p : Position G H q) :
    (active part p).card ≤ q := by
  exact (Finset.card_eraseNone_le _).trans ((Finset.card_image_le).trans (by simp))

theorem active_card_lt_vacant (part : Fin G.order → B) (p : Position G H q)
    (i : Fin q) (hi : p i = none) : (active part p).card < q := by
  have hm : none ∈ Finset.univ.image (fun j => (p j).map (fun a => part a.1)) :=
    Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by simp [hi]⟩
  have hc : (Finset.univ.image (fun j => (p j).map (fun a => part a.1))).card ≤ q :=
    Finset.card_image_le.trans (by simp)
  rw [active,Finset.card_eraseNone_of_mem hm]
  have hp : 0 < q := Nat.zero_le i.val |>.trans_lt i.isLt
  omega

theorem active_mono (part : Fin G.order → B) {p p' : Position G H q}
    (hp : Subposition p' p) : active part p' ⊆ active part p := by
  intro b hb
  obtain ⟨i,a,ha,rfl⟩ := (mem_active part p' b).mp hb
  exact (mem_active part p _).mpr ⟨i,a,hp i a ha,rfl⟩

theorem active_update_subset (part : Fin G.order → B) (p : Position G H q)
    (i : Fin q) (a : Fin G.order × Fin H.order) :
    active part (Function.update p i (some a)) ⊆ insert (part a.1) (active part p) := by
  intro b hb
  obtain ⟨j,c,hc,rfl⟩ := (mem_active part _ b).mp hb
  by_cases hj : j = i
  · subst j
    have he : a = c := by simpa using hc
    subst c
    exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem ((mem_active part p _).mpr
      ⟨j,c,by simpa only [Function.update_of_ne hj] using hc,rfl⟩)

theorem winning_of_block_families {Z : B → Type uVariable6}
    (part : Fin G.order → B)
    (maps : (∀ b, Z b) → (Fin G.order ≃ Fin H.order))
    (locality : ∀ ξ η v, ξ (part v) = η (part v) → maps ξ v = maps η v)
    (pool : Finset B → Set (∀ b, Z b))
    (empty : (pool ∅).Nonempty)
    (down : ∀ U V, U.card ≤ q → V ⊆ U → pool U ⊆ pool V)
    (extend : ∀ U, U.card < q → ∀ b ξ, ξ ∈ pool U →
      ∃ η ∈ pool (insert b U), ∀ c ∈ U, η c = ξ c)
    (safe : ∀ U ξ, ξ ∈ pool U → ∀ v w, part v ∈ U → part w ∈ U →
      (G.graph.Adj v w ↔ H.graph.Adj (maps ξ v) (maps ξ w))) :
    Winning (fun _ : Fin q => none : Position G H q) := by
  classical
  let S : Set (Position G H q) := {p | ∃ ξ, ξ ∈ pool (active part p) ∧
    ∀ i a, p i = some a → a.2 = maps ξ a.1}
  refine ⟨S,?_,?_,?_,?_⟩
  · obtain ⟨ξ,hξ⟩ := empty
    refine ⟨ξ,?_,by simp⟩
    have he : active part (fun _ : Fin q => none : Position G H q) = ∅ := by
      ext b
      simp [mem_active]
    simpa only [he] using hξ
  · rintro p ⟨ξ,hξ,hp⟩ i j a b ha hb
    have hpa := hp i a ha
    have hpb := hp j b hb
    rw [hpa,hpb]
    exact ⟨(maps ξ).injective.eq_iff.symm,safe _ ξ hξ _ _
      ((mem_active part p _).mpr ⟨i,a,ha,rfl⟩)
      ((mem_active part p _).mpr ⟨j,b,hb,rfl⟩)⟩
  · rintro p ⟨ξ,hξ,hp⟩ p' hp'
    exact ⟨ξ,down _ _ (active_card_le part p) (active_mono part hp') hξ,
      fun i a ha => hp i a (hp' i a ha)⟩
  · rintro p ⟨ξ,hξ,hp⟩ i hi
    have hex := fun b => extend (active part p) (active_card_lt_vacant part p i hi) b ξ hξ
    choose η hη hkeep using hex
    let θ : ∀ b, Z b := fun b => η b b
    refine ⟨maps θ,fun v => ?_⟩
    refine ⟨η (part v),down _ _ ?_ (active_update_subset part p i (v,maps θ v)) (hη _),?_⟩
    · exact (Finset.card_insert_le _ _).trans (by have := active_card_lt_vacant part p i hi; omega)
    · intro j a ha
      by_cases hj : j = i
      · subst j
        have he : (v,maps θ v) = a := by simpa using ha
        subst a
        exact locality θ (η (part v)) v rfl
      · have ha' : p j = some a := by simpa only [Function.update_of_ne hj] using ha
        exact (hp j a ha').trans (locality ξ (η (part v)) a.1
          (hkeep (part v) (part a.1) ((mem_active part p _).mpr ⟨j,a,ha',rfl⟩)).symm)
end VariableWL.Game

end OAI
