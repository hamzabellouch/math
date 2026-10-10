import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.TraceTagged
import OAI.Probability.CriticalPercolation.Exploration.Users

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.QueryTree
open FiniteEntropy

variable {E : Type*} [Fintype E]

noncomputable def inputMass (t : QueryTree E) (P : (E → Bool) → ℝ) (n : t.Node) : ℝ :=
  t.nodeMass (pushMass t.run P) n
noncomputable def inputNumerator (t : QueryTree E) (p : ℝ) (P : (E → Bool) → ℝ)
    (n : t.Node) : ℝ := t.nodeTrueMass (pushMass t.run P) n - p*t.inputMass P n
noncomputable def bitValue (ω : E → Bool) (e : E) : ℝ := if ω e then 1 else 0

lemma inputMass_eq_sum (t : QueryTree E) (P : (E → Bool) → ℝ) (n : t.Node) :
    t.inputMass P n = ∑ ω, if t.visits n ω then P ω else 0 := nodeMass_push t P n

lemma inputNumerator_eq_sum (t : QueryTree E) (p : ℝ) (P : (E → Bool) → ℝ) (n : t.Node) :
    t.inputNumerator p P n =
      ∑ ω, if t.visits n ω then P ω*(bitValue ω (t.bit n)-p) else 0 := by
  rw [inputNumerator, nodeTrueMass_push, inputMass_eq_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  cases t.visits n ω <;> cases hb : ω (t.bit n) <;> simp [hb,bitValue] <;> ring

lemma inputMass_nonneg (t : QueryTree E) (P : (E → Bool) → ℝ)
    (hP : ∀ ω, 0 ≤ P ω) (n : t.Node) : 0 ≤ t.inputMass P n := by
  rw [inputMass_eq_sum]
  apply Finset.sum_nonneg
  intro ω _; split_ifs; exact hP ω; exact le_rfl

lemma inputNumerator_eq_zero (t : QueryTree E) (p : ℝ) (P : (E → Bool) → ℝ)
    (hP : ∀ ω, 0 ≤ P ω) (n : t.Node) (hn : t.inputMass P n = 0) :
    t.inputNumerator p P n = 0 := by
  have ht : 0 ≤ t.nodeTrueMass (pushMass t.run P) n := by
    rw [nodeTrueMass_push]
    apply Finset.sum_nonneg
    intro ω _; split_ifs; exact hP ω; exact le_rfl
  have hl : t.nodeTrueMass (pushMass t.run P) n ≤ t.inputMass P n := by
    rw [nodeTrueMass_push, inputMass_eq_sum]
    apply Finset.sum_le_sum
    intro ω _
    split_ifs <;> simp_all
  unfold inputNumerator
  rw [hn]
  linarith

lemma charge_eq_input_sum (t : QueryTree E) (p : ℝ) (P : (E → Bool) → ℝ) :
    t.charge (fun r => (r-p)^2) (pushMass t.run P) =
      ∑ n, (t.inputNumerator p P n)^2 / t.inputMass P n :=
  quadratic_charge_eq_sum p t _

end CriticalPercolation.QueryTree

namespace CriticalPercolation.MarkedTree
open QueryTree FiniteEntropy

variable {E A : Type*} [Fintype E]

lemma pooled_inputMass (coord : A → E) (t : MarkedTree E A)
    (ht : t.Tagged coord) (hv : t.bare.Valid ∅) (P : (E → Bool) → ℝ) (a : A) :
    (∑ n : t.bare.Node, if t.nodeLabel n = a then t.bare.inputMass P n else 0) =
      ∑ ω, if (coord a,a) ∈ t.trace ω then P ω else 0 := by
  simp_rw [inputMass_eq_sum]
  simpa only [mul_one] using pooled_input_sum coord t ht hv P (fun _ _ => 1) a

lemma pooled_inputNumerator (coord : A → E) (t : MarkedTree E A)
    (ht : t.Tagged coord) (hv : t.bare.Valid ∅) (p : ℝ) (P : (E → Bool) → ℝ) (a : A) :
    (∑ n : t.bare.Node, if t.nodeLabel n = a then t.bare.inputNumerator p P n else 0) =
      ∑ ω, if (coord a,a) ∈ t.trace ω then P ω*(bitValue ω (coord a)-p) else 0 := by
  simp_rw [inputNumerator_eq_sum]
  exact pooled_input_sum coord t ht hv P (fun ω e => bitValue ω e-p) a

end CriticalPercolation.MarkedTree

namespace CriticalPercolation.OrderedQuery
open QueryTree MarkedTree Priority FiniteEntropy

variable {E I : Type*} [Fintype E] [Fintype I]

lemma fresh_weighted_input (t : I → QueryTree E) (ht : ∀ i, (t i).Valid ∅)
    (P : (E → Bool) → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (hover : ∀ ω, 0 < P ω → ∀ e, (users t ω e).card ≤ 4)
    (ω : E → Bool) (i : I) (n : (t i).Node) (c : ℝ) :
    (∑ o : Order I, orderWeight o i *
      (if (coord t ⟨i,n⟩, ⟨i,n⟩) ∈ (combined t o.val).trace ω then P ω*c else 0)) =
      if (t i).visits n ω then P ω*c else 0 := by
  simp_rw [fresh_order_node t _ i n (ht i) ω]
  by_cases hv : (t i).visits n ω
  · simp only [hv, true_and, ↓reduceIte]
    by_cases hz : P ω = 0
    · simp [hz]
    · have hs := otherUsers_card_le_three t i ω n hv (hover ω (lt_of_le_of_ne (hP ω) (Ne.symm hz)) _)
      have hw := weighted_first_identity i (otherUsers t i ω ((t i).bit n)) hs
      calc
        (∑ o : Order I, orderWeight o i *
            (if First o i (otherUsers t i ω ((t i).bit n)) then P ω*c else 0)) =
            (∑ o : Order I, if First o i (otherUsers t i ω ((t i).bit n)) then orderWeight o i else 0)*
              (P ω*c) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro o _
          split_ifs <;> simp
        _ = P ω*c := by rw [hw, one_mul]
  · simp [hv]

lemma weighted_pooled_numerator (t : I → QueryTree E) (ht : ∀ i, (t i).Valid ∅)
    (p : ℝ) (P : (E → Bool) → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (hover : ∀ ω, 0 < P ω → ∀ e, (users t ω e).card ≤ 4) (i : I) (n : (t i).Node) :
    (∑ o : Order I, orderWeight o i *
      ∑ g : (combined t o.val).bare.Node, if (combined t o.val).nodeLabel g = ⟨i,n⟩ then
        (combined t o.val).bare.inputNumerator p P g else 0) =
      (t i).inputNumerator p P n := by
  have hpool (o : Order I) := pooled_inputNumerator (coord t) (combined t o.val)
    (combined_tagged t o.val) (combined_valid t o.val) p P (⟨i,n⟩ : LocalNode t)
  simp_rw [hpool, Finset.mul_sum]
  rw [Finset.sum_comm, inputNumerator_eq_sum]
  apply Finset.sum_congr rfl
  intro ω _
  exact fresh_weighted_input t ht P hP hover ω i n (bitValue ω ((t i).bit n)-p)

lemma pooled_mass_le (t : I → QueryTree E) (ht : ∀ i, (t i).Valid ∅)
    (P : (E → Bool) → ℝ) (hP : ∀ ω, 0 ≤ P ω) (o : Order I) (i : I) (n : (t i).Node) :
    (∑ g : (combined t o.val).bare.Node, if (combined t o.val).nodeLabel g = ⟨i,n⟩ then
      (combined t o.val).bare.inputMass P g else 0) ≤ (t i).inputMass P n := by
  rw [pooled_inputMass (coord t) (combined t o.val) (combined_tagged t o.val)
    (combined_valid t o.val) P (⟨i,n⟩ : LocalNode t), inputMass_eq_sum]
  apply Finset.sum_le_sum
  intro ω _
  simp only [fresh_order_node t o i n (ht i) ω]
  split_ifs <;> simp_all

lemma weighted_pooled_mass_le (t : I → QueryTree E) (ht : ∀ i, (t i).Valid ∅)
    (P : (E → Bool) → ℝ) (hP : ∀ ω, 0 ≤ P ω) (i : I) (n : (t i).Node) :
    (∑ o : Order I, orderSquare o i *
      ∑ g : (combined t o.val).bare.Node, if (combined t o.val).nodeLabel g = ⟨i,n⟩ then
        (combined t o.val).bare.inputMass P g else 0) ≤ 16*(t i).inputMass P n := by
  calc
    _ ≤ ∑ o : Order I, orderSquare o i * (t i).inputMass P n :=
      Finset.sum_le_sum (fun o _ => mul_le_mul_of_nonneg_left
        (pooled_mass_le t ht P hP o i n) (orderSquare_nonneg o i))
    _ = _ := by rw [← Finset.sum_mul, sum_orderSquare]

end CriticalPercolation.OrderedQuery

end
end

end OAI
