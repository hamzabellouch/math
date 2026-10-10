import Mathlib
import OAI.Combinatorics.KMedian.PCP.Hadamard

namespace OAI

section Inline_PCPQuadratic

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section Quadratic
variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

structure QuadraticSystem (V E : Type) [Fintype V] [Fintype E] where
  form : E → BitVector (V × V)
  rhs : BitVector E

namespace QuadraticSystem
variable (Q : QuadraticSystem V E)

def Satisfies (a : BitVector V) : Prop := ∀ e, dot (tensor a a) (Q.form e) = Q.rhs e

def combination (t : BitVector E) : BitVector (V × V) := ∑ e, t e • Q.form e

omit [DecidableEq V] [DecidableEq E] in
@[simp] theorem combination_add (t u : BitVector E) :
    Q.combination (t+u) = Q.combination t + Q.combination u := by
  simp [combination, add_smul, sum_add_distrib]
omit [DecidableEq V] [DecidableEq E] in
@[simp] theorem combination_zero : Q.combination 0 = 0 := by simp [combination]

omit [DecidableEq V] in
@[simp] theorem combination_single (e : E) :
    Q.combination (Pi.single e 1) = Q.form e := by
  simp [combination, Pi.single_apply, ite_smul]

noncomputable def equationRate (h : BitVector (V × V) → Bit) : ℝ :=
  testRate (fun p : BitVector E × BitVector (V × V) =>
    derivative h (Q.combination p.1) p.2 ≠ dot Q.rhs p.1)

def equationDiscrepancy (h : BitVector (V × V) →+ Bit) : BitVector E →+ Bit where
  toFun t := h (Q.combination t) - dot Q.rhs t
  map_zero' := by simp
  map_add' := by intros; simp; ring

omit [DecidableEq V] in
@[simp] theorem equationDiscrepancy_single
    (h : BitVector (V × V) →+ Bit) (e : E) :
    Q.equationDiscrepancy h (Pi.single e 1) = h (Q.form e) - Q.rhs e := by
  simp [equationDiscrepancy, dot, Pi.single_apply, mul_ite]

theorem equation_transfer (h : BitVector (V × V) → Bit) :
    testRate (fun t => corrected h (Q.combination t) ≠ dot Q.rhs t) ≤
      Q.equationRate h + 2 * linearityRate h := by
  classical
  let P := fun p : BitVector E × BitVector (V × V) =>
    corrected h (Q.combination p.1) ≠ dot Q.rhs p.1
  let A := fun p : BitVector E × BitVector (V × V) =>
    derivative h (Q.combination p.1) p.2 ≠ dot Q.rhs p.1
  let B := fun p : BitVector E × BitVector (V × V) =>
    derivative h (Q.combination p.1) p.2 ≠ corrected h (Q.combination p.1)
  have hcover : ∀ p, P p → A p ∨ B p := by
    intro p hp
    by_contra hh
    simp only [A, B, not_or, not_not] at hh
    exact hp (hh.2.symm.trans hh.1)
  have hB : testRate B ≤ 2 * linearityRate h :=
    testRate_fibers_le (S := BitVector E) (T := BitVector (V × V))
      (fun t u => derivative h (Q.combination t) u ≠ corrected h (Q.combination t))
      (2 * linearityRate h) (fun t => corrective_query_error h (Q.combination t))
  have hh := testRate_union_bound hcover
  change testRate (fun p : BitVector E × BitVector (V × V) =>
    corrected h (Q.combination p.1) ≠ dot Q.rhs p.1) ≤ _ at hh
  rw [testRate_fst (fun t => corrected h (Q.combination t) ≠ dot Q.rhs t)] at hh
  have hA : testRate A = Q.equationRate h := rfl
  rw [hA] at hh
  linarith

omit [DecidableEq V] in
theorem equation_exact (h : BitVector (V × V) →+ Bit)
    (hr : testRate (fun t => h (Q.combination t) ≠ dot Q.rhs t) < 1/2) :
    ∀ e, h (Q.form e) = Q.rhs e := by
  classical
  intro e
  by_contra he
  have hn : Q.equationDiscrepancy h (Pi.single e 1) ≠ 0 := by
    simpa only [equationDiscrepancy_single, sub_ne_zero] using he
  have hb := linear_nonzero_rate (Q.equationDiscrepancy h) (Pi.single e 1) hn
  have heq : testRate (fun t => Q.equationDiscrepancy h t ≠ 0) =
      testRate (fun t => h (Q.combination t) ≠ dot Q.rhs t) := by
    apply testRate_congr
    intro t
    exact sub_ne_zero
  rw [heq] at hb
  linarith
end QuadraticSystem

noncomputable def multiplicationRate (f : BitVector V → Bit)
    (h : BitVector (V × V) → Bit) : ℝ :=
  testRate (fun p : (BitVector V × BitVector V) × BitVector (V × V) =>
    f p.1.1 * f p.1.2 ≠ derivative h (tensor p.1.1 p.1.2) p.2)

theorem multiplication_transfer (f : BitVector V → Bit) (h : BitVector (V × V) → Bit)
    (hf : linearityRate f < 1/6) :
    testRate (fun p : BitVector V × BitVector V =>
      corrected f p.1 * corrected f p.2 ≠ corrected h (tensor p.1 p.2)) ≤
      multiplicationRate f h + 4 * linearityRate f + 2 * linearityRate h := by
  classical
  let P := fun p : (BitVector V × BitVector V) × BitVector (V × V) =>
    corrected f p.1.1 * corrected f p.1.2 ≠ corrected h (tensor p.1.1 p.1.2)
  let A := fun p : (BitVector V × BitVector V) × BitVector (V × V) =>
    f p.1.1 * f p.1.2 ≠ derivative h (tensor p.1.1 p.1.2) p.2
  let B := fun p : (BitVector V × BitVector V) × BitVector (V × V) =>
    f p.1.1 ≠ corrected f p.1.1
  let C := fun p : (BitVector V × BitVector V) × BitVector (V × V) =>
    f p.1.2 ≠ corrected f p.1.2
  let D := fun p : (BitVector V × BitVector V) × BitVector (V × V) =>
    derivative h (tensor p.1.1 p.1.2) p.2 ≠ corrected h (tensor p.1.1 p.1.2)
  have hcover : ∀ p, P p → A p ∨ (B p ∨ (C p ∨ D p)) := by
    intro p hp
    by_contra hh
    simp only [A, B, C, D, not_or, not_not] at hh
    apply hp
    rw [← hh.2.1, ← hh.2.2.1]
    exact hh.1.trans hh.2.2.2
  have hB : testRate B ≤ 2 * linearityRate f := by
    change testRate (fun p : (BitVector V × BitVector V) × BitVector (V × V) =>
      f p.1.1 ≠ corrected f p.1.1) ≤ _
    rw [testRate_fst (fun q : BitVector V × BitVector V =>
      f q.1 ≠ corrected f q.1), testRate_fst (fun x : BitVector V => f x ≠ corrected f x)]
    exact corrected_distance f hf
  have hC : testRate C ≤ 2 * linearityRate f := by
    change testRate (fun p : (BitVector V × BitVector V) × BitVector (V × V) =>
      f p.1.2 ≠ corrected f p.1.2) ≤ _
    rw [testRate_fst (fun q : BitVector V × BitVector V =>
      f q.2 ≠ corrected f q.2), testRate_snd (fun x : BitVector V => f x ≠ corrected f x)]
    exact corrected_distance f hf
  have hD : testRate D ≤ 2 * linearityRate h :=
    testRate_fibers_le (S := BitVector V × BitVector V) (T := BitVector (V × V))
      (fun p u => derivative h (tensor p.1 p.2) u ≠ corrected h (tensor p.1 p.2))
      (2 * linearityRate h) (fun p => corrective_query_error h (tensor p.1 p.2))
  have hp := testRate_union_bound hcover
  have hc := testRate_or_le C D
  have hb := testRate_or_le B (fun p => C p ∨ D p)
  change testRate P ≤ testRate A + testRate (fun p => B p ∨ C p ∨ D p) at hp
  have hP : testRate P = testRate (fun p : BitVector V × BitVector V =>
      corrected f p.1 * corrected f p.2 ≠ corrected h (tensor p.1 p.2)) :=
    testRate_fst (T := BitVector (V × V))
      (fun p : BitVector V × BitVector V =>
        corrected f p.1 * corrected f p.2 ≠ corrected h (tensor p.1 p.2))
  rw [hP] at hp
  have hA : testRate A = multiplicationRate f h := rfl
  rw [hA] at hp
  linarith only [hp, hb, hc, hB, hC, hD]

end Quadratic
end MetricKMedian.PCP

end Inline_PCPQuadratic

end OAI
