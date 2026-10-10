import OAI.Combinatorics.HadwigerMatching.BasicMatching
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Combinatorics.SimpleGraph.Clique
import Lean.Elab.Tactic.Omega

namespace OAI

/-! # Sampled Graphs -/

noncomputable section
namespace HadwigerCounterexample
open HadwigerMatching Finset
variable {A V : Type*}

structure Holes (A : Type*) where
  rel : A → A → Prop
  sym {x y : A} : rel x y → rel y x
  irr (x : A) : ¬ rel x x
  ntri {x y z : A} : rel x y → rel y z → ¬ rel x z

namespace Holes

variable (H : Holes A)
def unit (p : A × A) := ¬H.rel p.1 p.2
def conflict (p q : A × A) := H.rel p.1 q.1 ∧ H.rel p.1 q.2 ∧ H.rel p.2 q.1 ∧ H.rel p.2 q.2

theorem no_self_conflict (p : A × A) : ¬ H.conflict p p := fun h => H.irr p.1 h.1

def graph (x : V → A) : SimpleGraph V where
  Adj i j := i ≠ j ∧ ¬H.rel (x i) (x j)
  symm := ⟨fun _ _ ⟨hne,h⟩ => ⟨hne.symm,fun h' => h (H.sym h')⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem indepNum_graph_le [Fintype V] (x : V → A) : (graph H x).indepNum ≤ 2 := by
  classical
  obtain ⟨S, hS, he⟩ := (graph H x).exists_isNIndepSet_indepNum
  rw [← he]
  by_contra h
  have hr : Fintype.card (Fin 3) ≤ Fintype.card S := by simp; omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hr
  let f : Fin 3 → V := fun i => e i
  have hf {i j} (h : i ≠ j) : H.rel (x (f i)) (x (f j)) := by
    by_contra hp
    apply hS (show f i ∈ (S : Set V) from (e i).property)
      (show f j ∈ (S : Set V) from (e j).property)
      (show f i ≠ f j from fun g => h (e.injective (Subtype.ext g)))
    exact ⟨fun g => h (e.injective (Subtype.ext g)), hp⟩
  exact H.ntri (hf (i:=0) (j:=1) (by decide)) (hf (j:=2) (by decide))
    (hf (by decide))

/-- Enumerate endpoints of an actual maximum connected matching on positions to
obtain pairwise disjoint ordered pairs; their raw unit types do not conflict. -/
theorem matching_pairs [Fintype V] (x : V → A) :
    let t := connectedMatchingNumber (graph H x)
    ∃ e : (Fin t ⊕ Fin t) → V, Function.Injective e ∧
      let f : Fin t → A × A := fun i => (x (e (.inl i)), x (e (.inr i)))
      (∀ i, H.unit (f i)) ∧ (∀ i j, ¬H.conflict (f i) (f j)) := by
  classical
  let G := graph H x
  let t := connectedMatchingNumber G
  obtain ⟨M,hM,hc⟩ := exists_matching_card_eq_number G
  have ht : Fintype.card M = t := by rw [Fintype.card_coe,hc]
  let m := (Fintype.equivFinOfCardEq ht).symm
  let m' (i : Fin t) : Finset V := (m i).val
  have hm i : m' i ∈ M := (m i).property
  have hex (i : Fin t) : ∃ v w : V, v ≠ w ∧ m' i = {v,w} :=
    card_eq_two.mp (hM.1 _ (hm i)).1
  choose v w hv he using hex
  let e := Sum.elim v w
  have hmem (i : Fin t ⊕ Fin t) : e i ∈ m' (Sum.elim id id i) := by
    cases i <;> simp [e,he]
  have hminj : Function.Injective m' := fun i j g => m.injective (Subtype.ext g)
  have hei : Function.Injective e := by
    intro i j h
    have hi : Sum.elim id id i = Sum.elim id id j := by
      by_contra hn
      have hh := hM.2.1 _ (hm _) _ (hm _) (hminj.ne hn)
      exact Finset.disjoint_left.mp hh (hmem i) (by rw [h]; exact hmem j)
    cases i <;> cases j <;> simp_all [e]
    exact hv _ h.symm
  refine ⟨e, hei, fun i => ?_, fun i j => ?_⟩
  · have h1 : v i ∈ m' i := by simp [he]
    have h2 : w i ∈ m' i := by simp [he]
    exact ((hM.1 _ (hm i)).2 h1 h2 (hv i)).2
  · by_cases h : i = j
    · subst j; exact no_self_conflict _ _
    · obtain ⟨a,ha,b,hb,hadj⟩ := hM.2.2 _ (hm i) _ (hm j) (hminj.ne h)
      have ha' : a = v i ∨ a = w i := by simpa [he] using ha
      have hb' : b = v j ∨ b = w j := by simpa [he] using hb
      intro hz
      apply hadj.2
      rcases ha' with h1|h1 <;> rcases hb' with h2|h2 <;> rw [h1,h2]
      · exact hz.1
      · exact hz.2.1
      · exact hz.2.2.1
      · exact hz.2.2.2
end Holes
end HadwigerCounterexample

end

end OAI
