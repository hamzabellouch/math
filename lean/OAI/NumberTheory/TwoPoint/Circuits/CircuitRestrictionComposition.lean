import OAI.NumberTheory.TwoPoint.Circuits.CircuitRestrictionDistribution

namespace OAI

/-! Applying two independent restrictions multiplies their live-coordinate
parameters. This is the distribution identity used for depth reduction. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def composeRestrictionBit (r s : Option Bool) : Option Bool :=
  match r with | none => s | some b => some b

def composeRestriction {n : ℕ} (ρ τ : PartialAssignment n) : PartialAssignment n :=
  fun i => composeRestrictionBit (ρ i) (τ i)

lemma composeRestriction_apply {n : ℕ} (ρ τ : PartialAssignment n) (x : BooleanCube n) :
    (composeRestriction ρ τ).apply x = ρ.apply (τ.apply x) := by
  funext i
  cases hρ : ρ i <;> simp [composeRestriction, composeRestrictionBit, PartialAssignment.apply, hρ]

lemma restriction_compose_atom (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (z : Option Bool) :
    ((restrictionBitLaw p hp hp1).product (restrictionBitLaw q hq hq1)).probability
      (fun b => composeRestrictionBit b.1 b.2 = z) =
      (restrictionBitLaw (p * q) (mul_nonneg hp hq) (by nlinarith)).weight z := by
  cases z with
  | none =>
    simp [FiniteLaw.probability, FiniteLaw.average, FiniteLaw.product,
      restrictionBitLaw, Fintype.sum_prod_type, Fintype.sum_option, composeRestrictionBit]
  | some b =>
    cases b <;>
      simp [FiniteLaw.probability, FiniteLaw.average, FiniteLaw.product,
        restrictionBitLaw, Fintype.sum_prod_type, Fintype.sum_option, composeRestrictionBit] <;>
      ring

theorem restrictionLaw_compose {n : ℕ} (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (f : PartialAssignment n → ℝ) :
    (restrictionLaw n p hp hp1).average (fun ρ =>
      (restrictionLaw n q hq hq1).average (fun τ => f (composeRestriction ρ τ))) =
        (restrictionLaw n (p * q) (mul_nonneg hp hq) (by nlinarith)).average f := by
  have hm := FiniteLaw.independent_average_map
    (fun _ : Fin n => (restrictionBitLaw p hp hp1).product (restrictionBitLaw q hq hq1))
    (fun _ : Fin n => restrictionBitLaw (p * q) (mul_nonneg hp hq) (by nlinarith))
    (fun _ b => composeRestrictionBit b.1 b.2)
    (fun _ z => restriction_compose_atom p q hp hp1 hq hq1 z) f
  have hpair := FiniteLaw.independent_average_pair
    (fun _ : Fin n => restrictionBitLaw p hp hp1)
    (fun _ : Fin n => restrictionBitLaw q hq hq1)
    (fun ρ τ => f (composeRestriction ρ τ))
  exact hpair.symm.trans hm

end TwoPointCorrelations

end OAI
