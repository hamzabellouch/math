import Mathlib
import OAI.Combinatorics.MatchingCount.Model
import OAI.Combinatorics.MatchingCount.Sampling.AssignmentEquiv

namespace OAI

namespace MatchingFPRAS.UnitRefresh

open Finset

variable {V L : Type*} [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L]

noncomputable def rankOrder (rank : L → ℕ) : List L :=
  (univ : Finset L).toList.mergeSort (fun a a' => decide (rank a'≤rank a))

omit [DecidableEq L] in
lemma rankOrder_mem [DecidableEq L] (rank : L → ℕ) (a : L) : a∈rankOrder rank := by
  unfold rankOrder
  rw [(List.mergeSort_perm _ _).mem_iff]
  simp

omit [DecidableEq L] in
lemma rankOrder_length [DecidableEq L] (rank : L → ℕ) : (rankOrder rank).length=Fintype.card L := by
  unfold rankOrder
  rw [(List.mergeSort_perm _ _).length_eq]
  simp

omit [DecidableEq L] in
lemma rankOrder_sorted [DecidableEq L] (rank : L → ℕ) :
    (rankOrder rank).Pairwise (fun a a' => rank a'≤rank a) := by
  let r := fun a a' : L => rank a'≤rank a
  let : Std.Total r := ⟨fun a b => le_total (rank b) (rank a)⟩
  let : IsTrans L r := ⟨fun a b c hab hbc => hbc.trans hab⟩
  exact List.pairwise_mergeSort' r _

lemma rankOrder_legal (b : V → Finset L) (rank : L → ℕ) (parent : L → Option L)
    (hb : RankedBags b rank parent) (hne : ∀ x,(b x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l) :
    LegalPlan b parent (rankOrder rank) univ := by
  apply rank_order_legal b rank parent hb hp _ (rankOrder_sorted rank)
  · intro x _; exact hne x
  · intro x _ a _; exact rankOrder_mem rank a

lemma active_univ (b : V → Finset L) (w : L → ℕ → ℕ) :
    activePartition b univ w=assignmentPartition b w := by
  change assignmentPartition (fun x : (univ : Finset V) => b x.val) w=assignmentPartition b w
  let e : (univ : Finset V) ≃ V :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x,mem_univ x⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  apply assignmentPartition_equiv _ _ e
  intro x; rfl

theorem ranked_tableDP_correct (b : V → Finset L) (rank : L → ℕ) (parent : L → Option L)
    (hb : RankedBags b rank parent) (hne : ∀ x,(b x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l) (w : L → ℕ → ℕ) :
    assignmentPartition b w=∏ l,tableDP b parent (rankOrder rank) univ w l 0 := by
  rw [← active_univ b w]
  exact tableDP_correct b parent _ _ (rankOrder_legal b rank parent hb hne hp) w

omit [Fintype L] [DecidableEq V] in
lemma private_le_card [Fintype L] [DecidableEq V] (b : V → Finset L) (R : Finset V) (l : L) :
    privateCount b R l≤Fintype.card V := by
  exact (card_filter_le _ _).trans (card_le_univ R)

omit [Fintype L] [DecidableEq V] in
lemma shared_le_card [Fintype L] [DecidableEq V] (b : V → Finset L) (R : Finset V) (l : L) :
    sharedCount b R l≤Fintype.card V := by
  exact (card_filter_le _ _).trans (card_le_univ R)

omit [Fintype L] in
lemma private_add_shared [Fintype L] (b : V → Finset L) (R : Finset V) (l : L) :
    privateCount b R l+sharedCount b R l≤Fintype.card V := by
  classical
  have he : (R.filter fun x => b x={l}) ∪ (R.filter fun x => l∈b x ∧ b x≠{l}) =
      R.filter (fun x => l∈b x) := by
    ext x
    simp only [mem_union,mem_filter]
    constructor
    · rintro (⟨hx,hb⟩|⟨hx,hl,_⟩)
      · exact ⟨hx,by simp [hb]⟩
      · exact ⟨hx,hl⟩
    · rintro ⟨hx,hl⟩
      by_cases h : b x={l}
      · exact Or.inl ⟨hx,h⟩
      · exact Or.inr ⟨hx,hl,h⟩
  have hd : Disjoint (R.filter fun x => b x={l}) (R.filter fun x => l∈b x ∧ b x≠{l}) := by
    apply disjoint_left.mpr
    intro x hx hx'
    exact (mem_filter.mp hx').2.2 (mem_filter.mp hx).2
  unfold privateCount sharedCount
  rw [← card_union_of_disjoint hd,he]
  exact (card_filter_le _ _).trans (card_le_univ R)

lemma advanceTable_congr (b : V → Finset L) (R : Finset V) (parent : L → Option L)
    (l : L) (w z : L → ℕ → ℕ) (B : ℕ)
    (h : ∀ a r,r≤B+Fintype.card V → w a r=z a r) (a : L) (r : ℕ) (hr : r≤B) :
    advanceTable b R parent l w a r=advanceTable b R parent l z a r := by
  classical
  have hs := shared_le_card b R l
  have hu := private_add_shared b R l
  unfold advanceTable
  cases hpar : parent l with
  | some p =>
    simp only
    unfold leafUpdate
    split_ifs
    · rfl
    · apply sum_congr rfl
      intro k hk
      have hk' : k ≤ sharedCount b R l := by simpa using (mem_range.mp hk)
      rw [h l _ (by omega),h _ _ (by omega)]
    · exact h a r (by omega)
  | none =>
    simp only
    unfold rootUpdate
    split_ifs
    · apply h
      have ht := (card_filter_le (s:=R) (p:=fun x => l∈b x)).trans (card_le_univ R)
      omega
    · exact h a r (by omega)

noncomputable def capTable (B : ℕ) (w : L → ℕ → ℕ) : L → ℕ → ℕ :=
  fun a r => if r≤B then w a r else 0

noncomputable def finiteDP (b : V → Finset L) (parent : L → Option L) :
    List L → Finset V → (L → ℕ → ℕ) → (L → ℕ → ℕ)
  | [],_,w => w
  | l::ls,R,w => finiteDP b parent ls (trim b R l)
      (capTable (Fintype.card V*ls.length)
        (advanceTable b R parent l w))

lemma finiteDP_correct (b : V → Finset L) (parent : L → Option L) (ls : List L)
    (R : Finset V) (w z : L → ℕ → ℕ)
    (h : ∀ a r,r≤Fintype.card V*ls.length → w a r=z a r) (a : L) :
    finiteDP b parent ls R w a 0=tableDP b parent ls R z a 0 := by
  induction ls generalizing R w z with
  | nil => exact h a 0 (by simp)
  | cons l ls ih =>
    apply ih
    intro a r hr
    rw [capTable,ite_eq_left hr]
    apply advanceTable_congr b R parent l w z (Fintype.card V*ls.length)
    · intro a r hr
      apply h
      simpa only [List.length_cons,Nat.mul_add,Nat.mul_one] using hr
    · exact hr

theorem finite_ranked_count (b : V → Finset L) (rank : L → ℕ) (parent : L → Option L)
    (hb : RankedBags b rank parent) (hne : ∀ x,(b x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l) (w : L → ℕ → ℕ) :
    assignmentPartition b w=∏ l,finiteDP b parent (rankOrder rank) univ
      (capTable (Fintype.card V*Fintype.card L) w) l 0 := by
  rw [ranked_tableDP_correct b rank parent hb hne hp w]
  apply prod_congr rfl
  intro a _
  symm
  apply finiteDP_correct
  intro a r hr
  rw [rankOrder_length] at hr
  exact ite_eq_left hr




abbrev withoutPair (a b : V) := {x : V // x≠a ∧ x≠b}

abbrev residualBags (bags : V → Finset L) (a b : V) : withoutPair a b → Finset L :=
  fun x => bags x.val

abbrev Partner (bags : V → Finset L) (a : V) :=
  {bc : V × L // bc.1≠a ∧ bc.2∈bags a ∧ bc.2∈bags bc.1}

omit [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L] in
lemma ColoredPairing.subtype_hext [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L]
    {bags : V → Finset L} {P Q : V → Prop}
    [DecidablePred P] [DecidablePred Q]
    (p : ColoredPairing (fun x : {x // P x} => bags x.val))
    (q : ColoredPairing (fun x : {x // Q x} => bags x.val))
    (hPQ : ∀ x,P x ↔ Q x)
    (hm : ∀ (x : {x // P x}) (y : {x // Q x}),x.val=y.val →
      (p.pair.mate x).val=(q.pair.mate y).val)
    (hc : ∀ (x : {x // P x}) (y : {x // Q x}),x.val=y.val → p.color x=q.color y) :
    HEq p q := by
  have he : P=Q := funext fun x => propext (hPQ x)
  subst Q
  apply heq_of_eq
  apply ColoredPairing.ext
  · ext x; exact hm x x rfl
  · funext x; exact hc x x rfl

def ColoredPairing.remove {bags : V → Finset L} (p : ColoredPairing bags) (a : V) :
    ColoredPairing (residualBags bags a (p.pair.mate a)) where
  pair := p.pair.remove a
  color x := p.color x.val
  allowed x := p.allowed x.val
  same_color x := p.same_color x.val

def ColoredPairing.insert {bags : V → Finset L} (a : V) (c : Partner bags a)
    (p : ColoredPairing (residualBags bags a c.val.1)) : ColoredPairing bags where
  pair := p.pair.insert a c.val.1 c.property.1
  color x := if hx : x=a ∨ x=c.val.1 then c.val.2 else p.color ⟨x,by tauto⟩
  allowed x := by
    dsimp
    split_ifs with hx
    · rcases hx with rfl|rfl
      · exact c.property.2.1
      · exact c.property.2.2
    · exact p.allowed _
  same_color x := by
    by_cases ha : x=a
    · subst x
      simp [Pairing.insert,c.property.1]
    by_cases hb : x=c.val.1
    · subst x
      simp [Pairing.insert,c.property.1]
    simp only [Pairing.insert,dite_eq_right ha,dite_eq_right hb]
    rw [dite_eq_right (by exact not_or.mpr (p.pair.mate ⟨x,ha,hb⟩).property),
      dite_eq_right (not_or.mpr ⟨ha,hb⟩)]
    exact p.same_color ⟨x,ha,hb⟩

omit [Fintype V] [Fintype L] [DecidableEq L] in
@[simp] lemma ColoredPairing.insert_color [Fintype V] [Fintype L] [DecidableEq L]
    {bags : V → Finset L} (a : V) (c : Partner bags a)
    (p : ColoredPairing (residualBags bags a c.val.1)) :
    (p.insert a c).color a=c.val.2 := by simp [ColoredPairing.insert]

omit [Fintype V] [Fintype L] [DecidableEq L] in
@[simp] lemma ColoredPairing.insert_color_residual [Fintype V] [Fintype L] [DecidableEq L]
    {bags : V → Finset L} (a : V)
    (c : Partner bags a) (p : ColoredPairing (residualBags bags a c.val.1))
    (x : withoutPair a c.val.1) :
    (p.insert a c).color x.val=p.color x := by
  simp [ColoredPairing.insert,x.property.1,x.property.2]

noncomputable def ColoredPairing.split {bags : V → Finset L} (a : V) :
    ColoredPairing bags ≃ Σ c : Partner bags a,ColoredPairing (residualBags bags a c.val.1) where
  toFun p := ⟨⟨(p.pair.mate a,p.color a),p.pair.no_fixed a,p.allowed a,
    by rw [← p.same_color a]; exact p.allowed _⟩,p.remove a⟩
  invFun q := q.2.insert a q.1
  left_inv p := by
    apply ColoredPairing.ext
    · ext x
      by_cases ha : x=a
      · subst x; simp [ColoredPairing.insert,Pairing.insert]
      by_cases hb : x=p.pair.mate a
      · subst x; simp [ColoredPairing.insert,Pairing.insert,p.pair.no_fixed,p.pair.involutive a]
      simp [ColoredPairing.insert,Pairing.insert,ColoredPairing.remove,Pairing.remove,ha,hb]
    · funext x
      by_cases ha : x=a
      · subst x; simp [ColoredPairing.insert]
      by_cases hb : x=p.pair.mate a
      · subst x; simp [ColoredPairing.insert,p.same_color]
      simp [ColoredPairing.insert,ColoredPairing.remove,ha,hb]
  right_inv q := by
    rcases q with ⟨c,p⟩
    apply Sigma.ext
    · apply Subtype.ext
      exact Prod.ext (Pairing.insert_at a c.val.1 c.property.1 p.pair) (ColoredPairing.insert_color a c p)
    · apply ColoredPairing.subtype_hext
      · intro x; simp only [ColoredPairing.insert,Pairing.insert_at]
      · intro x y hxy
        change (p.pair.insert a c.val.1 c.property.1).mate x.val=(p.pair.mate y).val
        rw [hxy]
        exact Pairing.insert_other _ _ _ _ y
      · intro x y hxy
        change (p.insert a c).color x.val=p.color y
        rw [hxy]
        exact ColoredPairing.insert_color_residual _ _ _ y

lemma partner_card (bags : V → Finset L) (a : V) :
    Fintype.card (Partner bags a)≤Fintype.card V*Fintype.card L := by
  exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_prod V L)

noncomputable def residualCount (bags : V → Finset L) (rank : L → ℕ)
    (parent : L → Option L) (a b : V) : ℕ :=
  ∏ l,finiteDP (residualBags bags a b) parent (rankOrder rank) univ
    (capTable (Fintype.card (withoutPair a b)*Fintype.card L) (fun _ => pairingCount)) l 0

lemma residualCount_eq (bags : V → Finset L) (rank : L → ℕ) (parent : L → Option L)
    (hb : RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l) (a b : V) :
    residualCount bags rank parent a b=Fintype.card (ColoredPairing (residualBags bags a b)) := by
  rw [coloredPairing_card]
  symm
  apply finite_ranked_count
  · intro x c hc d hd
    exact hb x.val c hc d hd
  · intro x; exact hne x.val
  · exact hp

theorem unit_self_reduction (bags : V → Finset L) (rank : L → ℕ) (parent : L → Option L)
    (hb : RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l) (a : V) :
    Fintype.card (ColoredPairing bags)=
      ∑ c : Partner bags a,residualCount bags rank parent a c.val.1 := by
  rw [Fintype.card_congr (ColoredPairing.split a),Fintype.card_sigma]
  apply sum_congr rfl
  intro c _
  exact (residualCount_eq bags rank parent hb hne hp a c.val.1).symm

end MatchingFPRAS.UnitRefresh

namespace MatchingFPRAS.UnitRefresh.Materialized

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Table := List (List ℕ)

def read (t : Table) (a r : ℕ) : ℕ := (t.getD a []).getD r 0

def tabulate (m B : ℕ) (f : Fin m → ℕ → ℕ) : Table :=
  List.ofFn fun a : Fin m => List.ofFn fun r : Fin (B+1) => f a r.val

lemma read_tabulate {m B : ℕ} (f : Fin m → ℕ → ℕ) (a : Fin m) (r : ℕ) :
    read (tabulate m B f) a.val r = if r≤B then f a r else 0 := by
  unfold read tabulate List.getD
  simp only [List.getElem?_ofFn, a.isLt, dite_eq_left, Option.getD_some]
  by_cases hr : r≤B
  · have h : r<B+1 := by omega
    simp [hr,h]
  · have h : ¬r<B+1 := by omega
    simp [hr,h]

lemma tabulate_length (m B : ℕ) (f : Fin m → ℕ → ℕ) :
    (tabulate m B f).length=m := by simp [tabulate]

lemma tabulate_rows {m B : ℕ} (f : Fin m → ℕ → ℕ) (row : List ℕ)
    (h : row ∈ tabulate m B f) : row.length=B+1 := by
  obtain ⟨a,rfl⟩ := List.mem_ofFn.mp h
  simp

lemma tabulate_cells (m B : ℕ) (f : Fin m → ℕ → ℕ) :
    ((tabulate m B f).map List.length).sum=m*(B+1) := by
  simp [tabulate,List.map_ofFn,List.sum_ofFn]

def entry {m : ℕ} (bags : V → Finset (Fin m)) (R : Finset V)
    (parent : Fin m → Option (Fin m)) (l a : Fin m) (t : Table) (r : ℕ) : ℕ :=
  match parent l with
  | none => if a=l then read t l.val ((R.filter fun x=>l∈bags x).card) else read t a.val r
  | some p => if a=l then 1 else if a=p then
      ∑ k∈range (sharedCount bags R l+1),
        (sharedCount bags R l).choose k * read t l.val (privateCount bags R l+k) *
          read t p.val (sharedCount bags R l-k+r)
      else read t a.val r

omit [Fintype V] [DecidableEq V] in
lemma entry_eq [Fintype V] [DecidableEq V] {m : ℕ} (bags : V → Finset (Fin m)) (R : Finset V)
    (parent : Fin m → Option (Fin m)) (l a : Fin m) (t : Table) (r : ℕ) :
    entry bags R parent l a t r =
      advanceTable bags R parent l (fun a r => read t a.val r) a r := by
  unfold entry advanceTable leafUpdate rootUpdate
  cases parent l <;> rfl

def update {m : ℕ} (bags : V → Finset (Fin m)) (R : Finset V)
    (parent : Fin m → Option (Fin m)) (l : Fin m) (B : ℕ) (t : Table) : Table :=
  tabulate m B (fun a r=>entry bags R parent l a t r)

lemma read_update {m : ℕ} (bags : V → Finset (Fin m)) (R : Finset V)
    (parent : Fin m → Option (Fin m)) (l a : Fin m) (B r : ℕ) (t : Table) :
    read (update bags R parent l B t) a.val r =
      capTable B (advanceTable bags R parent l (fun a r=>read t a.val r)) a r := by
  rw [update,read_tabulate]
  unfold capTable
  split_ifs <;> simp [entry_eq]

def run {m : ℕ} (bags : V → Finset (Fin m)) (parent : Fin m → Option (Fin m)) :
    List (Fin m) → Finset V → Table → Table
  | [],_,t => t
  | l::ls,R,t => run bags parent ls (trim bags R l)
      (update bags R parent l (Fintype.card V*ls.length) t)

lemma read_run {m : ℕ} (bags : V → Finset (Fin m)) (parent : Fin m → Option (Fin m))
    (ls : List (Fin m)) (R : Finset V) (t : Table) (a : Fin m) (r : ℕ) :
    read (run bags parent ls R t) a.val r =
      finiteDP bags parent ls R (fun a r=>read t a.val r) a r := by
  induction ls generalizing R t with
  | nil => rfl
  | cons l ls ih =>
    rw [run,finiteDP,ih]
    congr 2
    funext a r
    exact read_update bags R parent l a _ r t

def initial (m B : ℕ) : Table := tabulate m B (fun _=>pairingCount)

def count {m : ℕ} (bags : V → Finset (Fin m)) (parent : Fin m → Option (Fin m))
    (plan : List (Fin m)) : ℕ :=
  let t := run bags parent plan univ (initial m (Fintype.card V*m))
  ∏ a : Fin m,read t a.val 0

lemma count_eq {m : ℕ} (bags : V → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m))
    (hb : RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l) :
    count bags parent (rankOrder rank)=Fintype.card (ColoredPairing bags) := by
  rw [coloredPairing_card]
  change count bags parent (rankOrder rank)=assignmentPartition bags (fun _=>pairingCount)
  rw [finite_ranked_count bags rank parent hb hne hp]
  unfold count
  apply prod_congr rfl
  intro a _
  rw [read_run]
  congr 2
  funext b r
  simp only [initial,read_tabulate,capTable,Fintype.card_fin]

def cellsWritten {m : ℕ} (bags : V → Finset (Fin m)) : List (Fin m) → ℕ
  | [] => 0
  | _::ls => m*(Fintype.card V*ls.length+1)+cellsWritten bags ls

omit [DecidableEq V] in
lemma cellsWritten_bound [DecidableEq V] {m : ℕ} (bags : V → Finset (Fin m)) (ls : List (Fin m)) :
    cellsWritten bags ls ≤ ls.length*m*(Fintype.card V*ls.length+1) := by
  induction ls with
  | nil => simp [cellsWritten]
  | cons l ls ih =>
    simp only [cellsWritten,List.length_cons]
    calc
      _ ≤ m*(Fintype.card V*ls.length+1)+ls.length*m*(Fintype.card V*ls.length+1) :=
        Nat.add_le_add_left ih _
      _ = (ls.length+1)*m*(Fintype.card V*ls.length+1) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.le_succ _)) _)

end MatchingFPRAS.UnitRefresh.Materialized

end OAI
