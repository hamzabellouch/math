import OAI.NumberTheory.Ostmann.Characters.CycleMellin

namespace OAI

/-!
# Parseval for the independent moving coordinates on a cycle

The tensor products of unit characters form an orthogonal basis. This
finite identity makes the cycle projection energy a sum of products of
squared Mellin coefficients, with its exact probability normalization.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable local instance productMellinFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance productMellinDecidableEq {p : ℕ} :
    DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

noncomputable def productCharacter {p : ℕ} [Fact p.Prime] {I : Type*} [Fintype I]
    (ρ : I → MulChar (ZMod p) ℂ) (m : I → (ZMod p)ˣ) : ℂ := ∏ i, ρ i (m i)

theorem productCharacter_orthogonality {p : ℕ} [Fact p.Prime]
    {I : Type*} [Fintype I] [DecidableEq I]
    (ρ σ : I → MulChar (ZMod p) ℂ) :
    (∑ m : I → (ZMod p)ˣ, productCharacter ρ m * conj (productCharacter σ m)) =
      if ρ = σ then (Fintype.card (ZMod p)ˣ : ℂ) ^ Fintype.card I else 0 := by
  classical
  simp only [productCharacter, map_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : I) (z : (ZMod p)ˣ) => ρ i z * conj (σ i z))]
  simp_rw [mellin_orthogonality]
  by_cases h : ρ = σ
  · subst σ
    simp
  · simp only [h, ite_false]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [hi, ite_false]

/-- Probability-normalized Parseval for a finite product of unit groups. -/
theorem product_mellin_synthesis_parseval {p : ℕ} [Fact p.Prime]
    {I : Type*} [Fintype I] [DecidableEq I]
    (c : (I → MulChar (ZMod p) ℂ) → ℂ) :
    ((Fintype.card (ZMod p)ˣ : ℝ) ^ Fintype.card I)⁻¹ *
      (∑ m : I → (ZMod p)ˣ,
        ‖∑ ρ : I → MulChar (ZMod p) ℂ, c ρ * productCharacter ρ m‖ ^ 2) =
      ∑ ρ : I → MulChar (ZMod p) ℂ, ‖c ρ‖ ^ 2 := by
  classical
  let F : (I → (ZMod p)ˣ) → ℂ := fun m => ∑ ρ, c ρ * productCharacter ρ m
  have hc : (Fintype.card (ZMod p)ˣ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (∑ m : I → (ZMod p)ˣ, F m * conj (F m)) =
      (Fintype.card (ZMod p)ˣ : ℂ) ^ Fintype.card I *
        ∑ ρ : I → MulChar (ZMod p) ℂ, c ρ * conj (c ρ) := by
    simp only [F, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro σ _
    rw [Finset.sum_comm]
    calc
      _ = ∑ ρ : I → MulChar (ZMod p) ℂ, c ρ * conj (c σ) *
          ∑ m : I → (ZMod p)ˣ, productCharacter ρ m * conj (productCharacter σ m) := by
        apply Finset.sum_congr rfl
        intro ρ _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        ring
      _ = _ := by
        simp_rw [productCharacter_orthogonality]
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        ring
  have hsc : ((Fintype.card (ZMod p)ˣ : ℂ) ^ Fintype.card I)⁻¹ *
      (∑ m : I → (ZMod p)ˣ, F m * conj (F m)) =
        ∑ ρ : I → MulChar (ZMod p) ℂ, c ρ * conj (c ρ) := by
    rw [hs]
    field_simp
  simp_rw [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_sum] at hsc
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow,
    Complex.ofReal_natCast, Complex.ofReal_sum, F] using hsc

/-- The projected energy is the sum over the surviving cycle-character tuples. -/
theorem cycleAverage_product_energy {p : ℕ} [Fact p.Prime]
    {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → (ZMod p)ˣ → ℂ) (sign : I → ℤ) :
    ((Fintype.card (ZMod p)ˣ : ℝ) ^ Fintype.card I)⁻¹ *
      (∑ m : I → (ZMod p)ˣ, ‖cycleAverage sign (fun m => ∏ i : I, f i (m i)) m‖ ^ 2) =
      ∑ ρ : I → MulChar (ZMod p) ℂ,
        if (∏ i : I, (ρ i) ^ sign i) = 1 then
          ∏ i : I, ‖mellinCoefficient (f i) (ρ i)‖ ^ 2 else 0 := by
  classical
  let c : (I → MulChar (ZMod p) ℂ) → ℂ := fun ρ =>
    if (∏ i : I, (ρ i) ^ sign i) = 1 then ∏ i : I, mellinCoefficient (f i) (ρ i) else 0
  have hexp (m : I → (ZMod p)ˣ) :
      cycleAverage sign (fun m => ∏ i : I, f i (m i)) m =
        ∑ ρ : I → MulChar (ZMod p) ℂ, c ρ * productCharacter ρ m := by
    rw [cycleAverage_product_mellin]
    apply Finset.sum_congr rfl
    intro ρ _
    by_cases hr : (∏ i : I, (ρ i) ^ sign i) = 1
    · simp only [c, hr, ite_true, productCharacter, Finset.prod_mul_distrib]
    · simp only [c, hr, ite_false, zero_mul]
  simp_rw [hexp]
  rw [product_mellin_synthesis_parseval]
  apply Finset.sum_congr rfl
  intro ρ _
  by_cases hr : (∏ i : I, (ρ i) ^ sign i) = 1
  · simp only [c, hr, ite_true, norm_prod, Finset.prod_pow]
  · simp only [c, hr, ite_false, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]

end Ostmann

end OAI
