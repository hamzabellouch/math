import Mathlib
import OAI.Probability.LogConcave.JetEstimates.WireStep
import OAI.Probability.LogConcave.TensorGraphs.Live
import OAI.Probability.LogConcave.TensorGraphs.AdjointMatrix

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.Frontier
open scoped Classical

variable {E C : Type*} (a b : E → ℕ)

abbrev History (n : ℕ) := ∀k : Fin (n+1),Live a b k.val → C

def Consistent {n : ℕ} (h : History (C:=C) a b n) : Prop :=
  ∀k (hk : k<n) (e : Spectator a b k),
    h ⟨k+1,by omega⟩ ⟨e.val,by change a e.val≤k+1; have := e.property.1; omega,e.property.2⟩ =
    h ⟨k,by omega⟩ ⟨e.val,e.property.1,by change k<b e.val; have := e.property.2; omega⟩

def historyOf {n : ℕ} (c : E → C) : History (C:=C) a b n := fun _ e => c e.val

lemma historyOf_consistent {n : ℕ} (c : E → C) :
    Consistent a b (historyOf (n:=n) a b c) := by
  intro k hk e
  rfl

lemma consistent_color {n : ℕ} (hab : ∀e,a e<b e) (han : ∀e,a e≤n)
    {h : History (C:=C) a b n} (hh : Consistent a b h) (e : E)
    (k : ℕ) (hak : a e≤k) (hkn : k≤n) (hkb : k<b e) :
    h ⟨k,by omega⟩ ⟨e,hak,hkb⟩ =
    h ⟨a e,by have := han e; omega⟩ ⟨e,le_rfl,hab e⟩ := by
  induction k,hak using Nat.le_induction with
  | base => rfl
  | succ k hak ih =>
    have hk : k<n := by omega
    have he : a e≤k ∧ k+1<b e := ⟨hak,hkb⟩
    exact (hh k hk ⟨e,he⟩).trans (ih (by omega) (by omega))

noncomputable def historyEquiv {n : ℕ} (hab : ∀e,a e<b e) (han : ∀e,a e≤n) :
    (E → C) ≃ {h : History (C:=C) a b n // Consistent a b h} where
  toFun c := ⟨historyOf a b c,historyOf_consistent a b c⟩
  invFun h e := h.val ⟨a e,by have := han e; omega⟩ ⟨e,le_rfl,hab e⟩
  left_inv c := rfl
  right_inv h := by
    apply Subtype.ext
    funext k e
    exact (consistent_color a b hab han h.property e.val k.val
      e.property.1 (by have := k.isLt; omega) e.property.2).symm

theorem sum_consistent_histories [Fintype E] [Fintype C] {n : ℕ}
    (hab : ∀e,a e<b e) (han : ∀e,a e≤n)
    (F : History (C:=C) a b n → ℝ) :
    (∑h : History (C:=C) a b n,if Consistent a b h then F h else 0)=
      ∑c : E → C,F (historyOf a b c) := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (Consistent a b)]
  have hz : (∑i : {h : History (C:=C) a b n // ¬Consistent a b h},
      if Consistent a b i.val then F i.val else 0)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [i.property,ite_false]
  rw [hz,add_zero]
  simp only [Subtype.property,ite_true]
  exact ((historyEquiv (C:=C) a b hab han).sum_comp (fun h => F h.val)).symm
end LogConcaveSampling.Frontier
namespace LogConcaveSampling.Frontier
open scoped BigOperators Classical
open TensorEnergy

variable {E C : Type*} [Fintype E] [Fintype C]
    (a b : E → ℕ) (hab : ∀e,a e<b e)

def graphStep (A : ∀k,(Outgoing a k → C) → (Incoming b k → C) → ℝ) (k : ℕ) :
    (Live a b (k+1) → C) → (Live a b k → C) → ℝ :=
  wireStep (A k) (inputCoordinates a b hab k) (outputCoordinates a b hab k)

omit [Fintype E] [Fintype C] in
lemma consistent_iff_spectators {n : ℕ} (h : History (C:=C) a b n) :
    Consistent a b h ↔ ∀k : Fin n,
      (outputCoordinates a b hab k.val (h k.succ)).2 =
      (inputCoordinates a b hab k.val (h k.castSucc)).2 := by
  constructor
  · intro hh k
    funext e
    exact hh k.val k.isLt e
  · intro hh k hk e
    exact congrFun (hh ⟨k,hk⟩) e

omit [Fintype C] in

lemma pathWeight_graphStep
    (A : ∀k,(Outgoing a k → C) → (Incoming b k → C) → ℝ)
    (n : ℕ) (h : History (C:=C) a b n) :
    pathWeight (D:=fun k => Live a b k → C) (graphStep a b hab A) n h =
      if Consistent a b h then
        ∏k : Fin n,A k.val (outputCoordinates a b hab k.val (h k.succ)).1
          (inputCoordinates a b hab k.val (h k.castSucc)).1
      else 0 := by
  classical
  by_cases hc : Consistent a b h
  · rw [ite_eq_left hc]
    unfold pathWeight graphStep wireStep
    exact Finset.prod_congr rfl (fun k _ => by
      rw [ite_eq_left ((consistent_iff_spectators a b hab h).mp hc k),mul_one])
  · rw [ite_eq_right hc]
    have he : ∃k : Fin n,
      (outputCoordinates a b hab k.val (h k.succ)).2 ≠
      (inputCoordinates a b hab k.val (h k.castSucc)).2 := by
      simpa only [not_forall] using
        (mt (consistent_iff_spectators a b hab h).mpr hc)
    obtain ⟨k,hk⟩ := he
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp only [graphStep,wireStep,ite_eq_right hk,mul_zero]

theorem coordinate_sum_eq_circuit
    (A : ∀k,(Outgoing a k → C) → (Incoming b k → C) → ℝ) (n : ℕ)
    (han : ∀e,a e≤n) (B : (Live a b 0 → C) → (Live a b n → C) → ℝ) :
    (∑c : E → C,(∏k : Fin n,A k.val (fun e => c e.val) (fun e => c e.val))*
      B (fun e => c e.val) (fun e => c e.val)) =
    ∑i,∑j,circuit (D:=fun k => Live a b k → C) (graphStep a b hab A) n j i*B i j := by
  have hs := sum_consistent_histories (C:=C) a b hab han
    (fun h => (∏k : Fin n,A k.val (outputCoordinates a b hab k.val (h k.succ)).1
      (inputCoordinates a b hab k.val (h k.castSucc)).1)*B (h 0) (h (Fin.last n)))
  have hp := circuit_path_expansion (D:=fun k => Live a b k → C) (graphStep a b hab A) n B
  have hs' : (∑h : History (C:=C) a b n,if Consistent a b h then
      (∏k : Fin n,A k.val (outputCoordinates a b hab k.val (h k.succ)).1
        (inputCoordinates a b hab k.val (h k.castSucc)).1)*B (h 0) (h (Fin.last n)) else 0)=
      (∑c : E → C,(∏k : Fin n,A k.val (fun e => c e.val) (fun e => c e.val))*
        B (fun e => c e.val) (fun e => c e.val)) := hs
  rw [←hs',←hp]
  apply Finset.sum_congr rfl
  intro h hh
  rw [pathWeight_graphStep]
  split_ifs <;> simp only [zero_mul]

include hab in

theorem coordinate_contraction_bound
    (A : ∀k,(Outgoing a k → C) → (Incoming b k → C) → ℝ) (M : ℕ → ℝ)
    (hM : ∀k,0≤M k) (hA : ∀k,Bound (A k) ((M k)^2))
    (n : ℕ) (han : ∀e,a e≤n) (close : (Live a b 0 → C) ≃ (Live a b n → C)) :
    |∑c : E → C,(∏k : Fin n,A k.val (fun e => c e.val) (fun e => c e.val))*
      (if (fun e : Live a b n => c e.val)=close (fun e : Live a b 0 => c e.val)
        then 1 else 0)| ≤
      (Fintype.card (Live a b 0 → C):ℝ)*(∏k∈Finset.range n,M k) := by
  rw [coordinate_sum_eq_circuit a b hab A n han
    (fun i j => if j=close i then 1 else 0)]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  exact closed_wire_circuit_bound (D:=fun k => Live a b k → C)
    (I:=fun k => Incoming b k → C) (O:=fun k => Outgoing a k → C)
    (S:=fun k => Spectator a b k → C) A M hM hA
    (inputCoordinates a b hab) (outputCoordinates a b hab) n close
end LogConcaveSampling.Frontier
namespace LogConcaveSampling.GraphSchedule
open scoped Classical

variable {V U : Type*} [Fintype V] (key : V → ℕ) (src dst : U → V)

abbrev Edge (q : ℕ) := U ⊕ (Fin q ⊕ Fin q)

def length : ℕ := Finset.univ.sup key+1

lemma key_lt_length (v : V) : key v<length key :=
  lt_of_le_of_lt (Finset.le_sup (f:=key) (Finset.mem_univ v)) (Nat.lt_succ_self _)

def emit (_first last : V) (q : ℕ) : Edge (U:=U) q → ℕ
  | Sum.inl e => min (key (src e)+1) (key (dst e)+1)
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr _) => key last+1

def absorb (first _last : V) (q : ℕ) : Edge (U:=U) q → ℕ
  | Sum.inl e => max (key (src e)+1) (key (dst e)+1)
  | Sum.inr (Sum.inl _) => key first+1
  | Sum.inr (Sum.inr _) => length key+1

include key in
lemma emit_lt_absorb (hkey : Function.Injective key) (hne : ∀e,src e≠dst e)
    (first last : V) (q : ℕ) (e : Edge (U:=U) q) :
    emit key src dst first last q e<absorb key src dst first last q e := by
  rcases e with e | (i|i)
  · exact min_lt_max.mpr (by
      intro he
      have hh : key (src e)=key (dst e) := by omega
      exact hne e (hkey hh))
  · exact Nat.zero_lt_succ _
  · exact Nat.add_lt_add_right (key_lt_length key last) 1

lemma emit_le_length (first last : V) (q : ℕ) (e : Edge (U:=U) q) :
    emit key src dst first last q e≤length key := by
  rcases e with e | (i|i)
  · exact (min_le_left _ _).trans (key_lt_length key (src e))
  · exact Nat.zero_le _
  · exact key_lt_length key last

noncomputable def inputEdges (first last : V) (q : ℕ) :
    Frontier.Live (emit key src dst first last q) (absorb key src dst first last q) 0 ≃ Fin q where
  toFun e := by
    rcases e with ⟨e,he⟩
    rcases e with e | (i|i)
    · simp only [emit] at he
      omega
    · exact i
    · simp only [emit] at he
      omega
  invFun i := ⟨Sum.inr (Sum.inl i),Nat.zero_le _,Nat.zero_lt_succ _⟩
  left_inv e := by
    rcases e with ⟨e,he⟩
    rcases e with e | (i|i)
    · simp only [emit] at he
      omega
    · rfl
    · simp only [emit] at he
      omega
  right_inv i := rfl

noncomputable def outputEdges (first last : V) (q : ℕ) :
    Frontier.Live (emit key src dst first last q) (absorb key src dst first last q)
      (length key) ≃ Fin q where
  toFun e := by
    rcases e with ⟨e,he⟩
    rcases e with e | (i|i)
    · have hs := key_lt_length key (src e)
      have ht := key_lt_length key (dst e)
      simp only [absorb] at he
      omega
    · have hs := key_lt_length key first
      simp only [absorb] at he
      omega
    · exact i
  invFun i := ⟨Sum.inr (Sum.inr i),key_lt_length key last,Nat.lt_succ_self _⟩
  left_inv e := by
    rcases e with ⟨e,he⟩
    rcases e with e | (i|i)
    · have hs := key_lt_length key (src e)
      have ht := key_lt_length key (dst e)
      simp only [absorb] at he
      omega
    · have hs := key_lt_length key first
      simp only [absorb] at he
      omega
    · rfl
  right_inv i := rfl

noncomputable def close {C : Type*} (first last : V) (q : ℕ) :
    (Frontier.Live (emit key src dst first last q) (absorb key src dst first last q) 0 → C) ≃
      (Frontier.Live (emit key src dst first last q) (absorb key src dst first last q)
        (length key) → C) :=
  Equiv.arrowCongr ((inputEdges key src dst first last q).trans
    (outputEdges key src dst first last q).symm) (Equiv.refl C)

lemma input_card [Fintype U] (first last : V) (q d : ℕ) :
    Fintype.card (Frontier.Live (emit key src dst first last q)
      (absorb key src dst first last q) 0 → Fin d)=d^q := by
  rw [Fintype.card_fun,Fintype.card_fin,Fintype.card_congr (inputEdges key src dst first last q),
    Fintype.card_fin]
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.GraphSchedule
open scoped Classical

variable {V U : Type*} [Fintype V] (key : V → ℕ) (src dst : U → V)

def Adjacent (u v : V) : Prop :=
  ∃e,(src e=u ∧ dst e=v) ∨ (src e=v ∧ dst e=u)

lemma incident_sides (first last : V) (q : ℕ) {u v : V}
    (h : Adjacent src dst u v) (huv : key u<key v) :
    Nonempty (Frontier.Outgoing (emit key src dst first last q) (key u)) ∧
    Nonempty (Frontier.Incoming (absorb key src dst first last q) (key v)) := by
  obtain ⟨e,he⟩ := h
  rcases he with ⟨hs,ht⟩ | ⟨hs,ht⟩
  · constructor
    · exact ⟨⟨Sum.inl e,by simp only [emit,hs,ht,min_eq_left (Nat.add_le_add_right huv.le 1)]⟩⟩
    · exact ⟨⟨Sum.inl e,by simp only [absorb,hs,ht,max_eq_right (Nat.add_le_add_right huv.le 1)]⟩⟩
  · constructor
    · exact ⟨⟨Sum.inl e,by simp only [emit,hs,ht,min_eq_right (Nat.add_le_add_right huv.le 1)]⟩⟩
    · exact ⟨⟨Sum.inl e,by simp only [absorb,hs,ht,max_eq_left (Nat.add_le_add_right huv.le 1)]⟩⟩

theorem factor_splits_nonempty (first last : V) (q : ℕ) (hq : 0<q)
    (horder : ∀v,(v=first ∨ ∃u,Adjacent src dst u v ∧ key u<key v) ∧
      (v=last ∨ ∃w,Adjacent src dst v w ∧ key v<key w)) (v : V) :
    Nonempty (Frontier.Incoming (absorb key src dst first last q) (key v)) ∧
    Nonempty (Frontier.Outgoing (emit key src dst first last q) (key v)) := by
  obtain ⟨hi,ho⟩ := horder v
  constructor
  · rcases hi with rfl | ⟨u,hu,hk⟩
    · exact ⟨⟨Sum.inr (Sum.inl ⟨0,hq⟩),rfl⟩⟩
    · exact (incident_sides key src dst first last q hu hk).2
  · rcases ho with rfl | ⟨w,hw,hk⟩
    · exact ⟨⟨Sum.inr (Sum.inr ⟨0,hq⟩),rfl⟩⟩
    · exact (incident_sides key src dst first last q hw hk).1
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.AdjointRemoval
variable {n : ℕ} {S : State (Fin (n+1))}

abbrev InternalEdge (β : Fin n → ℕ) := ((k : Fin n) × Fin (β k)) ⊕ Fin (n+1)

def edgeSource (β : Fin n → ℕ) : InternalEdge β → TargetVertex S
  | Sum.inl e => Sum.inl e.1.castSucc
  | Sum.inr i => Sum.inl i

def edgeTarget (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) : InternalEdge β → TargetVertex S
  | Sum.inl e => Sum.inl e.1.succ
  | Sum.inr i => destination hS i

lemma internal_adjacent (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (e : InternalEdge β) :
    Adjacent hS (edgeSource (S:=S) β e) (edgeTarget hS β e) := by
  rcases e with ⟨k,i⟩ | i
  · exact Or.inl ⟨k,Or.inl ⟨rfl,rfl⟩⟩
  · exact Or.inr ⟨i,Or.inl ⟨rfl,rfl⟩⟩

lemma internal_source_ne (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (e : InternalEdge β) :
    edgeSource (S:=S) β e ≠ edgeTarget hS β e :=
  adjacent_ne hS (internal_adjacent hS β e)

lemma adjacent_has_edge (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (hβ : ∀k,0<β k) {u v : TargetVertex S} (h : Adjacent hS u v) :
    GraphSchedule.Adjacent (edgeSource (S:=S) β) (edgeTarget hS β) u v := by
  rcases h with ⟨k,h⟩ | ⟨i,h⟩
  · refine ⟨Sum.inl ⟨k,⟨0,hβ k⟩⟩,?_⟩
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl ⟨rfl,rfl⟩
    · exact Or.inr ⟨rfl,rfl⟩
  · refine ⟨Sum.inr i,?_⟩
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl ⟨rfl,rfl⟩
    · exact Or.inr ⟨rfl,rfl⟩

theorem actual_removal_schedule
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (hβ : ∀k,0<β k) :
    ∃key : TargetVertex S → ℕ,Function.Injective key ∧
      ∀(q : ℕ),0<q → ∀v : TargetVertex S,
        Nonempty (Frontier.Incoming
          (GraphSchedule.absorb key (edgeSource (S:=S) β) (edgeTarget hS β)
            (Sum.inl 0) (Sum.inl (Fin.last n)) q) (key v)) ∧
        Nonempty (Frontier.Outgoing
          (GraphSchedule.emit key (edgeSource (S:=S) β) (edgeTarget hS β)
            (Sum.inl 0) (Sum.inl (Fin.last n)) q) (key v)) := by
  obtain ⟨key,hkey,_,hsplit⟩ := actual_removal_graph_order hS
  refine ⟨key,hkey,fun q hq v => ?_⟩
  apply GraphSchedule.factor_splits_nonempty key (edgeSource (S:=S) β) (edgeTarget hS β)
    (Sum.inl 0) (Sum.inl (Fin.last n)) q hq _ v
  intro w
  obtain ⟨hi,ho⟩ := hsplit w
  constructor
  · rcases hi with h | ⟨u,hu,hk⟩
    · exact Or.inl h
    · exact Or.inr ⟨u,adjacent_has_edge hS β hβ hu,hk⟩
  · rcases ho with h | ⟨u,hu,hk⟩
    · exact Or.inl h
    · exact Or.inr ⟨u,adjacent_has_edge hS β hβ hu,hk⟩
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.GraphSchedule
open scoped Classical

variable {V U C : Type*} [Fintype V] (key : V → ℕ) (src dst : U → V)
local instance edgeDecEqC (q : ℕ) : DecidableEq (Edge (U:=U) q) := Classical.decEq _
local instance finDecEqC (d : ℕ) : DecidableEq (Fin d) := Classical.decEq _

lemma close_output_apply (first last : V) (q : ℕ)
    (x : Frontier.Live (emit key src dst first last q) (absorb key src dst first last q) 0 → C)
    (i : Fin q) :
    close key src dst first last q x
      ⟨Sum.inr (Sum.inr i),key_lt_length key last,Nat.lt_succ_self _⟩=
    x ⟨Sum.inr (Sum.inl i),Nat.zero_le _,Nat.zero_lt_succ _⟩ := rfl

lemma closing_iff (first last : V) (q : ℕ) (c : Edge (U:=U) q → C) :
    (fun e : Frontier.Live (emit key src dst first last q)
      (absorb key src dst first last q) (length key) => c e.val)=
        close key src dst first last q
          (fun e : Frontier.Live (emit key src dst first last q)
            (absorb key src dst first last q) 0 => c e.val) ↔
    ∀i : Fin q,c (Sum.inr (Sum.inr i))=c (Sum.inr (Sum.inl i)) := by
  constructor
  · intro h i
    exact congrFun h ⟨Sum.inr (Sum.inr i),key_lt_length key last,Nat.lt_succ_self _⟩
  · intro h
    funext e
    obtain ⟨i,rfl⟩ := (outputEdges key src dst first last q).symm.surjective e
    exact h i

def duplicate {q : ℕ} (c : U ⊕ Fin q → C) : Edge (U:=U) q → C
  | Sum.inl u => c (Sum.inl u)
  | Sum.inr (Sum.inl i) => c (Sum.inr i)
  | Sum.inr (Sum.inr i) => c (Sum.inr i)

noncomputable def cutColorEquiv (q : ℕ) :
    (U ⊕ Fin q → C) ≃
      {c : Edge (U:=U) q → C // ∀i : Fin q,c (Sum.inr (Sum.inr i))=c (Sum.inr (Sum.inl i))} where
  toFun c := ⟨duplicate c,fun _ => rfl⟩
  invFun c := Sum.elim (fun u => c.val (Sum.inl u)) (fun i => c.val (Sum.inr (Sum.inl i)))
  left_inv c := by funext e; cases e <;> rfl
  right_inv c := by
    apply Subtype.ext
    funext e
    rcases e with e | (i|i)
    · rfl
    · rfl
    · exact (c.property i).symm

theorem sum_closed_coordinates [Fintype U] [Fintype C]
    (first last : V) (q : ℕ) (F : (Edge (U:=U) q → C) → ℝ) :
    (∑c : Edge (U:=U) q → C,F c*
      (if (fun e : Frontier.Live (emit key src dst first last q)
        (absorb key src dst first last q) (length key) => c e.val)=
          close key src dst first last q
            (fun e : Frontier.Live (emit key src dst first last q)
              (absorb key src dst first last q) 0 => c e.val) then 1 else 0))=
      ∑c : U ⊕ Fin q → C,F (duplicate c) := by
  simp_rw [closing_iff,mul_ite,mul_one,mul_zero]
  let P (c : Edge (U:=U) q → C) := ∀i : Fin q,c (Sum.inr (Sum.inr i))=c (Sum.inr (Sum.inl i))
  rw [←Fintype.sum_subtype_add_sum_subtype P]
  have hz : (∑i : {c : Edge (U:=U) q → C // ¬P c},if P i.val then F i.val else 0)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [i.property,ite_false]
  change (∑i : {c : Edge (U:=U) q → C // P c},if P i.val then F i.val else 0)+
    (∑i : {c : Edge (U:=U) q → C // ¬P c},if P i.val then F i.val else 0)=_
  rw [hz,add_zero]
  simp only [Subtype.property,ite_true]
  exact ((cutColorEquiv (U:=U) (C:=C) q).sum_comp (fun c => F c.val)).symm
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.GraphSchedule
open scoped BigOperators Classical
open TensorEnergy

variable {V U : Type*} [Fintype V] [Fintype U]
local instance edgeDecEq (q : ℕ) : DecidableEq (Edge (U:=U) q) := Classical.decEq _
local instance finDecEq (d : ℕ) : DecidableEq (Fin d) := Classical.decEq _

theorem scheduled_coordinate_bound (key : V → ℕ) (src dst : U → V)
    (hkey : Function.Injective key) (hne : ∀e,src e≠dst e)
    (first last : V) (q d : ℕ)
    (A : ∀k,(Frontier.Outgoing (emit key src dst first last q) k → Fin d) →
      (Frontier.Incoming (absorb key src dst first last q) k → Fin d) → ℝ)
    (M : ℕ → ℝ) (hM : ∀k,0≤M k) (hA : ∀k,Bound (A k) ((M k)^2)) :
    |∑c : Edge (U:=U) q → Fin d,
      (∏k : Fin (length key),A k.val (fun e => c e.val) (fun e => c e.val))*
      (if (fun e : Frontier.Live (emit key src dst first last q)
          (absorb key src dst first last q) (length key) => c e.val)=
        close key src dst first last q
          (fun e : Frontier.Live (emit key src dst first last q)
            (absorb key src dst first last q) 0 => c e.val) then 1 else 0)|≤
      (d:ℝ)^q*(∏k∈Finset.range (length key),M k) := by
  calc
    _ ≤ (Fintype.card (Frontier.Live (emit key src dst first last q)
      (absorb key src dst first last q) 0 → Fin d):ℝ)*
        (∏k∈Finset.range (length key),M k) := by
      exact Frontier.coordinate_contraction_bound (E:=Edge (U:=U) q) (C:=Fin d)
        (emit key src dst first last q) (absorb key src dst first last q)
        (emit_lt_absorb key src dst hkey hne first last q) A M hM hA (length key)
        (emit_le_length key src dst first last q) (close key src dst first last q)
    _ = _ := by
      rw [Fintype.card_fun,Fintype.card_fin,
        Fintype.card_congr (inputEdges key src dst first last q),Fintype.card_fin,Nat.cast_pow]
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.GraphSchedule
open scoped BigOperators Classical
open TensorEnergy

variable {V U : Type*} [Fintype V] [Fintype U]
local instance edgeDecEqR (q : ℕ) : DecidableEq (Edge (U:=U) q) := Classical.decEq _
local instance finDecEqR (d : ℕ) : DecidableEq (Fin d) := Classical.decEq _

theorem reduced_coordinate_bound (key : V → ℕ) (src dst : U → V)
    (hkey : Function.Injective key) (hne : ∀e,src e≠dst e)
    (first last : V) (q d : ℕ)
    (A : ∀k,(Frontier.Outgoing (emit key src dst first last q) k → Fin d) →
      (Frontier.Incoming (absorb key src dst first last q) k → Fin d) → ℝ)
    (M : ℕ → ℝ) (hM : ∀k,0≤M k) (hA : ∀k,Bound (A k) ((M k)^2)) :
    |∑c : U ⊕ Fin q → Fin d,
      ∏k : Fin (length key),A k.val (fun e => duplicate c e.val) (fun e => duplicate c e.val)|≤
      (d:ℝ)^q*(∏k∈Finset.range (length key),M k) := by
  rw [←sum_closed_coordinates key src dst first last q
    (fun c => ∏k : Fin (length key),A k.val (fun e => c e.val) (fun e => c e.val))]
  exact scheduled_coordinate_bound key src dst hkey hne first last q d A M hM hA
end LogConcaveSampling.GraphSchedule

end UpperProof
end
end
end

end OAI
