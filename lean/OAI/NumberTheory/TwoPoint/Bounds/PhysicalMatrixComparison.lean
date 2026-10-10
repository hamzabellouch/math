import OAI.NumberTheory.TwoPoint.Bounds.ShiftTraceComparison
import OAI.NumberTheory.TwoPoint.Bounds.ShiftedIntegerPaths
import OAI.NumberTheory.TwoPoint.Bounds.FiniteAverages

namespace OAI

/-! Compare physical matrix moments by their signed closed scalar words.
Copy gates remain fixed while only the arithmetic origin is averaged. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def FiniteLaw.uniform (α : Type*) [Fintype α] [Nonempty α] : FiniteLaw α where
  weight _ := (Fintype.card α : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by simp

lemma FiniteLaw.uniform_average {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    (FiniteLaw.uniform α).average f = uniformAverage f := by
  simp only [FiniteLaw.average, FiniteLaw.uniform, uniformAverage, ← mul_sum, div_eq_mul_inv]
  ring

theorem physicalMatrix_moment_comparison {D V α β : Type*}
    [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype α] [Fintype β]
    (embed : V → D × ℤ) (hinj : Function.Injective embed)
    (Q : Finset ℕ) (tuple : D → ℕ) (h : ℕ) (gate : D → ℤ → ℤ → Prop)
    (weight : SignedStep → ℤ → ℝ)
    (hflip : ∀ t n, weight t.flip (n + t.displacement h) = weight t n)
    (μ : FiniteLaw α) (ν : FiniteLaw β) (origin : α → ℤ) (origin' : β → ℤ)
    (k : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hcompare : ∀ (i : V) (a b : Fin k → D × (Q × Bool)),
      shiftWordEnd (integerShiftNext Q tuple h) (embed i) a =
        shiftWordEnd (integerShiftNext Q tuple h) (embed i) b →
      |μ.average (fun x => scalarWalkProduct h weight ((embed i).2 + origin x)
          (integerClosedWordCode Q tuple (a, b))) -
        ν.average (fun x => scalarWalkProduct h weight ((embed i).2 + origin' x)
          (integerClosedWordCode Q tuple (a, b)))| ≤ ε) :
    |μ.average (fun x => matrixFrobeniusSq (shiftMatrix embed (integerShiftNext Q tuple h)
        (physicalShiftWeight Q tuple h gate (fun t n => weight t (n + origin x))) ^ k)) -
      ν.average (fun x => matrixFrobeniusSq (shiftMatrix embed (integerShiftNext Q tuple h)
        (physicalShiftWeight Q tuple h gate (fun t n => weight t (n + origin' x))) ^ k))| ≤
      (Fintype.card V : ℝ) * (Fintype.card (D × (Q × Bool)) : ℝ) ^ (2 * k) * ε := by
  apply shiftMatrix_moment_comparison embed hinj
  intro i a b
  by_cases hend : shiftWordEnd (integerShiftNext Q tuple h) (embed i) a =
      shiftWordEnd (integerShiftNext Q tuple h) (embed i) b
  · have ha (x : α) : shiftClosedWeight embed (integerShiftNext Q tuple h)
        (physicalShiftWeight Q tuple h gate (fun t n => weight t (n + origin x))) k i a b =
        (integerPathMask embed Q tuple h gate (embed i) a *
          integerPathMask embed Q tuple h gate (embed i) b) *
          scalarWalkProduct h weight ((embed i).2 + origin x) (integerClosedWordCode Q tuple (a, b)) := by
      rw [shiftClosedWeight, ite_eq_left hend]
      exact physicalShiftWord_closed_pair embed Q tuple h gate weight hflip _ _ a b hend
    have hb (x : β) : shiftClosedWeight embed (integerShiftNext Q tuple h)
        (physicalShiftWeight Q tuple h gate (fun t n => weight t (n + origin' x))) k i a b =
        (integerPathMask embed Q tuple h gate (embed i) a *
          integerPathMask embed Q tuple h gate (embed i) b) *
          scalarWalkProduct h weight ((embed i).2 + origin' x) (integerClosedWordCode Q tuple (a, b)) := by
      rw [shiftClosedWeight, ite_eq_left hend]
      exact physicalShiftWord_closed_pair embed Q tuple h gate weight hflip _ _ a b hend
    simp_rw [ha, hb]
    rcases integerPathMask_zero_or_one embed Q tuple h gate (embed i) a with hma | hma <;>
      rcases integerPathMask_zero_or_one embed Q tuple h gate (embed i) b with hmb | hmb
    all_goals simp only [hma, hmb, zero_mul, mul_zero, one_mul, FiniteLaw.average_const,
      sub_self, abs_zero]
    all_goals first | exact hε | exact hcompare i a b hend
  · simpa only [shiftClosedWeight, hend, ite_false, FiniteLaw.average_const, sub_self, abs_zero] using hε

end TwoPointCorrelations

end OAI
