import OAI.NumberTheory.TwoPoint.Bounds.UniformResidueTranslation
import OAI.NumberTheory.TwoPoint.Bounds.MaskedWeightPeriodicity
import OAI.NumberTheory.TwoPoint.Bounds.ShiftTraceComparison

namespace OAI

/-! Reduce the actual translated matrix moment to signed closed-word expectations. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

variable {D V : Type*} [DecidableEq D] [Fintype V]

theorem physicalClosedPair_average_abs_le {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (embed : V → D × ℤ) (Q : Finset ℕ) (tuple : D → ℕ)
    (gate : D → ℤ → ℤ → Prop) (weight : SignedStep → ℤ → ℝ)
    (hflip : ∀ t n, weight t.flip (n + t.displacement h) = weight t n)
    {k : ℕ} (x : D × ℤ) (a b : Fin k → D × (Q × Bool))
    (hend : shiftWordEnd (integerShiftNext Q tuple h) x a =
      shiftWordEnd (integerShiftNext Q tuple h) x b)
    (hperiod : ∀ t ∈ integerClosedWordCode Q tuple (a, b), ∀ n m : ℤ,
      (∀ p : ↥(data.P ∪ data.Q), (n : ZMod p.val) = (m : ZMod p.val)) →
        weight t n = weight t m) :
    |(data.residueLaw B hB).average (fun r =>
      shiftWordWeight embed (integerShiftNext Q tuple h)
        (physicalShiftWeight Q tuple h gate
          (fun t n => weight t (n + data.residueOrigin r))) x a *
      shiftWordWeight embed (integerShiftNext Q tuple h)
        (physicalShiftWeight Q tuple h gate
          (fun t n => weight t (n + data.residueOrigin r))) x b)| ≤
      |(data.residueLaw B hB).average (fun r =>
        scalarWalkProduct h weight (data.residueOrigin r) (integerClosedWordCode Q tuple (a, b)))| := by
  have htrans := data.residue_average_translate hB
    (fun n => scalarWalkProduct h weight n (integerClosedWordCode Q tuple (a, b)))
    (fun n m hnm => scalarWalkProduct_residue_congr (data.P ∪ data.Q) h weight _
      (fun t ht z z' hz => hperiod t ht z z' (fun p => hz p.val p.property)) n m
      (fun p hp => hnm ⟨p, hp⟩)) x.2
  have hpair : (data.residueLaw B hB).average (fun r =>
      shiftWordWeight embed (integerShiftNext Q tuple h)
        (physicalShiftWeight Q tuple h gate
          (fun t n => weight t (n + data.residueOrigin r))) x a *
      shiftWordWeight embed (integerShiftNext Q tuple h)
        (physicalShiftWeight Q tuple h gate
          (fun t n => weight t (n + data.residueOrigin r))) x b) =
      (integerPathMask embed Q tuple h gate x a * integerPathMask embed Q tuple h gate x b) *
        (data.residueLaw B hB).average (fun r =>
          scalarWalkProduct h weight (data.residueOrigin r) (integerClosedWordCode Q tuple (a, b))) := by
    calc
      _ = (data.residueLaw B hB).average (fun r =>
          (integerPathMask embed Q tuple h gate x a * integerPathMask embed Q tuple h gate x b) *
            scalarWalkProduct h weight (data.residueOrigin r + x.2)
              (integerClosedWordCode Q tuple (a, b))) := by
        apply congrArg (data.residueLaw B hB).average
        funext r
        rw [physicalShiftWord_closed_pair embed Q tuple h gate weight hflip _ x a b hend,
          add_comm x.2]
      _ = _ := by
        rw [← htrans]
        simp only [FiniteLaw.average, mul_sum]
        apply sum_congr rfl
        intro r _
        ring
  rw [hpair]
  rcases integerPathMask_zero_or_one embed Q tuple h gate x a with ha | ha <;>
    rcases integerPathMask_zero_or_one embed Q tuple h gate x b with hb | hb <;>
    simp [ha, hb]

variable [Fintype D] [DecidableEq V]

theorem physicalResidueMatrix_moment_le {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (embed : V → D × ℤ) (hinj : Function.Injective embed)
    (Q : Finset ℕ) (tuple : D → ℕ) (gate : D → ℤ → ℤ → Prop)
    (weight : SignedStep → ℤ → ℝ)
    (hflip : ∀ t n, weight t.flip (n + t.displacement h) = weight t n) (k : ℕ)
    (hperiod : ∀ (a b : Fin k → D × (Q × Bool)),
      ∀ t ∈ integerClosedWordCode Q tuple (a, b), ∀ n m : ℤ,
        (∀ p : ↥(data.P ∪ data.Q), (n : ZMod p.val) = (m : ZMod p.val)) →
          weight t n = weight t m) :
    (data.residueLaw B hB).average (fun r =>
      matrixFrobeniusSq (shiftMatrix embed (integerShiftNext Q tuple h)
        (physicalShiftWeight Q tuple h gate (fun t n => weight t (n + data.residueOrigin r))) ^ k)) ≤
      ∑ i : V, ∑ a : Fin k → D × (Q × Bool), ∑ b : Fin k → D × (Q × Bool),
        if shiftWordEnd (integerShiftNext Q tuple h) (embed i) a =
          shiftWordEnd (integerShiftNext Q tuple h) (embed i) b ∧
            integerPathMask embed Q tuple h gate (embed i) a ≠ 0 ∧
            integerPathMask embed Q tuple h gate (embed i) b ≠ 0 then
          |(data.residueLaw B hB).average (fun r => scalarWalkProduct h weight
            (data.residueOrigin r) (integerClosedWordCode Q tuple (a, b)))| else 0 := by
  rw [average_shiftMatrix_moment embed hinj]
  apply sum_le_sum
  intro i _
  apply sum_le_sum
  intro a _
  apply sum_le_sum
  intro b _
  by_cases hend : shiftWordEnd (integerShiftNext Q tuple h) (embed i) a =
      shiftWordEnd (integerShiftNext Q tuple h) (embed i) b
  · by_cases ha : integerPathMask embed Q tuple h gate (embed i) a = 0
    · simp only [shiftClosedWeight, hend, ite_true, physicalShiftWord_product, ha,
        zero_mul, ne_eq, not_true_eq_false, false_and, and_false, ite_false,
        FiniteLaw.average_const, le_refl]
    · by_cases hb : integerPathMask embed Q tuple h gate (embed i) b = 0
      · simp only [shiftClosedWeight, hend, ite_true, physicalShiftWord_product, hb,
          zero_mul, mul_zero, ne_eq, not_true_eq_false, and_false, ite_false,
          FiniteLaw.average_const, le_refl]
      · simp only [shiftClosedWeight, hend, ha, hb, ne_eq, not_false_eq_true,
          and_self, ite_true]
        exact (le_abs_self _).trans
          (physicalClosedPair_average_abs_le data hB embed Q tuple gate weight hflip
            (embed i) a b hend (hperiod a b))
  · simp [shiftClosedWeight, hend]

end TwoPointCorrelations

end OAI
