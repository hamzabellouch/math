import Mathlib
import OAI.Combinatorics.KMedian.Model
import OAI.Combinatorics.KMedian.Probability.Conditioning
import OAI.Combinatorics.KMedian.Sparse.SparseIntegerLaw
import OAI.Combinatorics.KMedian.Sparse.SparseRealExpectation

namespace OAI

section
section
namespace MetricKMedian.SparseSelect
variable {α : Type}

def best (P : α → Bool) (cost : α → ℚ) : List α → Option α
  | [] => none
  | a::L => if P a then
      match best P cost L with
      | none => some a
      | some b => some (if cost a ≤ cost b then a else b)
    else best P cost L

theorem best_spec (P : α → Bool) (cost : α → ℚ) (L : List α) :
    (best P cost L=none ↔ ∀ a∈L,P a=false) ∧
    ∀ a, best P cost L=some a → a∈L ∧ P a=true ∧ ∀ b∈L,P b=true → cost a ≤ cost b := by
  induction L with
  | nil => simp [best]
  | cons a L ih =>
    by_cases ha : P a=true
    · cases hb : best P cost L with
      | none =>
        have hL := ih.1.mp hb
        simp only [best,ha,ite_true,hb]
        constructor
        · simp only [Option.some_ne_none,List.mem_cons,false_iff]
          intro hh
          have := hh a (Or.inl rfl)
          simp [ha] at this
        · intro b h
          have he : a=b := Option.some.inj h
          subst b
          refine ⟨List.mem_cons_self,ha,?_⟩
          intro b hmem hP
          rcases List.mem_cons.mp hmem with he | he
          · subst b; exact le_rfl
          · have hf := hL b he
            rw [hP] at hf
            contradiction
      | some b =>
        obtain ⟨hbmem,hbP,hmin⟩ := ih.2 b hb
        simp only [best,ha,ite_true,hb]
        constructor
        · simp only [Option.some_ne_none,List.mem_cons,false_iff]
          intro hh
          have := hh a (Or.inl rfl)
          simp [ha] at this
        · intro z hz
          by_cases hab : cost a ≤ cost b
          · simp only [ite_eq_left hab,Option.some.injEq] at hz
            subst z
            refine ⟨List.mem_cons_self,ha,?_⟩
            intro z hz hP
            rcases List.mem_cons.mp hz with he | he
            · subst z; exact le_rfl
            · exact hab.trans (hmin z he hP)
          · simp only [ite_eq_right hab,Option.some.injEq] at hz
            subst z
            refine ⟨List.mem_cons_of_mem a hbmem,hbP,?_⟩
            intro z hz hP
            rcases List.mem_cons.mp hz with he | he
            · subst z; exact le_of_lt (lt_of_not_ge hab)
            · exact hmin z he hP
    · have haf : P a=false := Bool.eq_false_iff.mpr ha
      simp only [best,haf,Bool.false_eq_true,ite_false]
      constructor
      · rw [ih.1]
        constructor
        · intro h b hb
          rcases List.mem_cons.mp hb with he | he
          · subst b; exact haf
          · exact h b he
        · intro h b hb
          exact h b (List.mem_cons_of_mem a hb)
      · intro b hb
        obtain ⟨hbmem,hbP,hmin⟩ := ih.2 b hb
        refine ⟨List.mem_cons_of_mem a hbmem,hbP,?_⟩
        intro z hz hP
        rcases List.mem_cons.mp hz with he | he
        · subst z
          rw [haf] at hP
          contradiction
        · exact hmin z he hP

def choose (μ : SparseIntegerLaw α) (P : α → Bool) (cost : α → ℚ) : Option α :=
  best P cost μ.states.toList

theorem choose_spec (μ : SparseIntegerLaw α) (P : α → Bool) (cost : α → ℚ)
    (a : α) (ha : choose μ P cost=some a) :
    P a=true ∧ ∀ i : Fin μ.length, P μ.states[i.val]=true → cost a ≤ cost μ.states[i.val] := by
  have hs := (best_spec P cost μ.states.toList).2 a ha
  refine ⟨hs.2.1,fun i hi => hs.2.2 _ ?_ hi⟩
  exact Vector.mem_toList_iff.mpr (Vector.getElem_mem i.isLt)

theorem choose_bound (μ : SparseIntegerLaw α) (P : α → Bool) (cost : α → ℚ)
    {p C : ℝ} (hp : 0 < p)
    (hP : p ≤ μ.realIndex.prob (fun i => P μ.states[i.val]=true))
    (hcost : ∀ a,0 ≤ cost a)
    (hE : μ.expectation (fun a => (cost a:ℝ)) ≤ C) :
    ∃ a, choose μ P cost=some a ∧ P a=true ∧ (cost a:ℝ) ≤ C/p := by
  obtain ⟨i,_hi,hgood,hbound⟩ := μ.realIndex.select_success_bound
    (fun i => P μ.states[i.val]=true) (fun i => (cost μ.states[i.val]:ℝ)) hp hP
    (fun i => by exact_mod_cast hcost _) hE
  cases hb : choose μ P cost with
  | none =>
    have hz := (best_spec P cost μ.states.toList).1.mp hb _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem i.isLt))
    rw [hgood] at hz
    contradiction
  | some a =>
    obtain ⟨ha,hmin⟩ := choose_spec μ P cost a hb
    refine ⟨a,rfl,ha,?_⟩
    exact (show (cost a:ℝ) ≤ (cost μ.states[i.val]:ℝ) by exact_mod_cast hmin i hgood).trans hbound

end MetricKMedian.SparseSelect
end
end

end OAI
