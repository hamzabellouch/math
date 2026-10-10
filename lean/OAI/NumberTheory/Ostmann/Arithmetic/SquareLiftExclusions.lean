import Mathlib.Analysis.Complex.Basic
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticLifts

namespace OAI

/-! # Dropping the prime-square exclusions in a two-history expansion -/

namespace Ostmann

open scoped BigOperators

/-- Uniform pairs over the fixed giant residues modulo `p`. -/
abbrev SquareLiftPairs (p : ℕ) (x₀ y₀ : ZMod p) :=
  {x : ZMod (p ^ 2) // squareReduction p x = x₀} ×
    {y : ZMod (p ^ 2) // squareReduction p y = y₀}

private def zeroLiftEquiv {p : ℕ} (a : (ZMod (p ^ 2))ˣ)
    (b : ZMod (p ^ 2)) (x₀ y₀ : ZMod p) :
    {v : SquareLiftPairs p x₀ y₀ // (a : ZMod (p ^ 2)) * v.1.1 + b * v.2.1 = 0} ≃
    {xy : ZMod (p ^ 2) × ZMod (p ^ 2) //
      squareReduction p xy.1 = x₀ ∧ squareReduction p xy.2 = y₀ ∧
        (a : ZMod (p ^ 2)) * xy.1 + b * xy.2 = 0} where
  toFun v := ⟨(v.1.1, v.1.2), v.1.1.property, v.1.2.property, v.property⟩
  invFun v := ⟨(⟨v.1.1, v.property.1⟩, ⟨v.1.2, v.property.2.1⟩), v.property.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_zeroLift {p : ℕ} [Fact p.Prime]
    (a : (ZMod (p ^ 2))ˣ) (b : ZMod (p ^ 2)) (x₀ y₀ : ZMod p)
    (hbase : squareReduction p a * x₀ + squareReduction p b * y₀ = 0) :
    Fintype.card {v : SquareLiftPairs p x₀ y₀ //
      (a : ZMod (p ^ 2)) * v.1.1 + b * v.2.1 = 0} = p := by
  rw [Fintype.card_congr (zeroLiftEquiv a b x₀ y₀),
    Fintype.card_congr (liftedLineEquiv (squareReduction p) a b x₀ y₀ hbase),
    card_squareReduction_fiber]

/-- All forbidden prime-square zeros, one for each occurrence of the prime. -/
noncomputable def squareLiftBad {I : Type*} [Fintype I] {p : ℕ} [Fact p.Prime]
    (a : I → (ZMod (p ^ 2))ˣ) (b : I → ZMod (p ^ 2)) (x₀ y₀ : ZMod p) :
    Finset (SquareLiftPairs p x₀ y₀) := by
  classical
  exact Finset.univ.filter fun v => ∃ i, (a i : ZMod (p ^ 2)) * v.1.1 + b i * v.2.1 = 0

theorem card_squareLiftBad_le {I : Type*} [Fintype I] {p : ℕ} [Fact p.Prime]
    (a : I → (ZMod (p ^ 2))ˣ) (b : I → ZMod (p ^ 2)) (x₀ y₀ : ZMod p)
    (hbase : ∀ i, squareReduction p (a i) * x₀ + squareReduction p (b i) * y₀ = 0) :
    (squareLiftBad a b x₀ y₀).card ≤ Fintype.card I * p := by
  classical
  have heq : squareLiftBad a b x₀ y₀ = Finset.univ.biUnion
      (fun i => Finset.univ.filter fun v : SquareLiftPairs p x₀ y₀ =>
        (a i : ZMod (p ^ 2)) * v.1.1 + b i * v.2.1 = 0) := by
    ext v
    simp [squareLiftBad]
  rw [heq]
  refine (Finset.card_biUnion_le).trans_eq ?_
  have hc (i : I) : (Finset.univ.filter fun v : SquareLiftPairs p x₀ y₀ =>
      (a i : ZMod (p ^ 2)) * v.1.1 + b i * v.2.1 = 0).card = p := by
    simpa only [Fintype.card_subtype] using card_zeroLift (a i) (b i) x₀ y₀ (hbase i)
  simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- A bounded integrand loses at most `B * (# occurrences) / p` when all
prime-square exclusions are imposed. No independence of the exclusions is used. -/
theorem square_lift_removed_mass_le {I : Type*} [Fintype I] {p : ℕ} [Fact p.Prime]
    (a : I → (ZMod (p ^ 2))ˣ) (b : I → ZMod (p ^ 2)) (x₀ y₀ : ZMod p)
    (hbase : ∀ i, squareReduction p (a i) * x₀ + squareReduction p (b i) * y₀ = 0)
    (F : SquareLiftPairs p x₀ y₀ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ v, ‖F v‖ ≤ B) :
    ‖∑ v ∈ squareLiftBad a b x₀ y₀, F v‖ / (p : ℝ) ^ 2 ≤
      B * (Fintype.card I : ℝ) / p := by
  classical
  have hcard : ((squareLiftBad a b x₀ y₀).card : ℝ) ≤ (Fintype.card I : ℝ) * p :=
    by exact_mod_cast card_squareLiftBad_le a b x₀ y₀ hbase
  have hsum : ‖∑ v ∈ squareLiftBad a b x₀ y₀, F v‖ ≤ B * (Fintype.card I : ℝ) * p := by
    calc
      _ ≤ ∑ v ∈ squareLiftBad a b x₀ y₀, ‖F v‖ := norm_sum_le _ _
      _ ≤ ∑ _v ∈ squareLiftBad a b x₀ y₀, B := Finset.sum_le_sum fun v _ => hF v
      _ = B * ((squareLiftBad a b x₀ y₀).card : ℝ) := by simp [mul_comm]
      _ ≤ _ := by nlinarith
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  calc
    _ ≤ (B * (Fintype.card I : ℝ) * p) / (p : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hsum (sq_nonneg _)
    _ = _ := by field_simp

/-- The form used in both giant environments: the second giant has a nonzero
residue, and every occurrence has a nonzero row. This supplies the unit
coefficient needed for the lift count rather than assuming it separately. -/
theorem square_lift_nonzero_rows_removed_mass_le {I : Type*} [Fintype I]
    {p : ℕ} [Fact p.Prime] (a b : I → ZMod (p ^ 2)) (x₀ y₀ : ZMod p)
    (hy : y₀ ≠ 0)
    (hrow : ∀ i, squareReduction p (a i) ≠ 0 ∨ squareReduction p (b i) ≠ 0)
    (hbase : ∀ i, squareReduction p (a i) * x₀ + squareReduction p (b i) * y₀ = 0)
    (F : SquareLiftPairs p x₀ y₀ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ v, ‖F v‖ ≤ B) :
    ‖∑ v ∈ Finset.univ.filter (fun v : SquareLiftPairs p x₀ y₀ =>
      ∃ i, a i * v.1.1 + b i * v.2.1 = 0), F v‖ / (p : ℝ) ^ 2 ≤
      B * (Fintype.card I : ℝ) / p := by
  classical
  let u : I → (ZMod (p ^ 2))ˣ := fun i =>
    (square_line_first_isUnit (a i) (b i) x₀ y₀ hy (hrow i) (hbase i)).unit
  have hu (i : I) : (u i : ZMod (p ^ 2)) = a i := IsUnit.unit_spec _
  have hb : ∀ i, squareReduction p (u i) * x₀ + squareReduction p (b i) * y₀ = 0 := by
    intro i
    rw [hu]
    exact hbase i
  simpa only [squareLiftBad, hu] using
    square_lift_removed_mass_le u b x₀ y₀ hb F B hB hF

end Ostmann

end OAI
