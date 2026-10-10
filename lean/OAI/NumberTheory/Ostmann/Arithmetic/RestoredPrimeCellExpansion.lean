import OAI.NumberTheory.Ostmann.Construction.OriginalPrimeCellExpansion
import OAI.NumberTheory.Ostmann.Arithmetic.RestoredHarmonicCells
import OAI.NumberTheory.Ostmann.Construction.OriginalBulkResidues

namespace OAI

/-! # Keep the deleted-set normalization in the original cell expansion -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem harmonic_mass_ne_zero_of_sdiff (S D : Finset ℕ)
    (h : (∑ p ∈ S \ D, (p : ℝ)⁻¹) ≠ 0) : (∑ p ∈ S, (p : ℝ)⁻¹) ≠ 0 := by
  have hp : 0 < ∑ p ∈ S \ D, (p : ℝ)⁻¹ :=
    lt_of_le_of_ne (Finset.sum_nonneg fun p _ => by positivity) (Ne.symm h)
  exact ne_of_gt (hp.trans_le (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
    (fun p _ _ => by positivity)))

/-- Restoring a prime atom multiplies the full-set normalized prior by
exactly the ratio of its harmonic masses, not by a new probability law. -/
theorem restored_prime_prior_atom (P S D : Finset ℕ)
    (h : (∑ p ∈ S \ D, (p : ℝ)⁻¹) ≠ 0) (p : P) :
    ((∑ t ∈ S \ D, (t : ℝ)⁻¹)⁻¹ * ∑ t ∈ S, (t : ℝ)⁻¹) * primeSubsetPrior P S p =
      if (p : ℕ) ∈ S then (∑ t ∈ S \ D, (t : ℝ)⁻¹)⁻¹ * (p : ℝ)⁻¹ else 0 := by
  unfold primeSubsetPrior
  by_cases hp : (p : ℕ) ∈ S
  · rw [ite_eq_left hp, ite_eq_left hp, div_eq_mul_inv]
    have hs := harmonic_mass_ne_zero_of_sdiff S D h
    calc
      _ = (∑ t ∈ S \ D, (t : ℝ)⁻¹)⁻¹ * (p : ℝ)⁻¹ *
          ((∑ t ∈ S, (t : ℝ)⁻¹) * (∑ t ∈ S, (t : ℝ)⁻¹)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hs, mul_one]
  · simp [hp]

theorem restored_prime_cell_expansion {J C : Type*} [Fintype J] [Fintype C]
    (P : Finset ℕ) (q : J → ℕ) (a : J → C → ℕ) (u v : J → C → ℝ) (c₀ : C)
    (hP : ∀ j, primeCellSupport (q j) (a j) (u j) (v j) ⊆ P)
    (hsep : ∀ j c d, c ≠ d →
      ¬Nat.ModEq (q j) (a j c) (a j d) ∨ v j c ≤ u j d ∨ v j d ≤ u j c)
    (D : J → Finset ℕ)
    (hD : ∀ j, (∑ p ∈ primeCellSupport (q j) (a j) (u j) (v j) \ D j, (p : ℝ)⁻¹) ≠ 0)
    (f : (J → C) → BulkIntegrand J) :
    let S := fun j => primeCellSupport (q j) (a j) (u j) (v j)
    let Z := fun j => (∑ p ∈ S j \ D j, (p : ℝ)⁻¹)⁻¹
    ((∏ j, Z j : ℝ) : ℂ) * ∑ c : J → C,
      ∫ y, f c y ∂Measure.pi (fun j => primeLogCellMeasure (q j) (a j (c j)) (u j (c j)) (v j (c j))) =
    ∑ x : J → P,
      ((∏ j, (if (x j : ℕ) ∈ S j then Z j * (x j : ℝ)⁻¹ else 0) : ℝ) : ℂ) *
        f (fun j => primeCellLabel (q j) (a j) (u j) (v j) c₀ (x j)) (fun j => Real.log (x j : ℕ)) := by
  let S := fun j => primeCellSupport (q j) (a j) (u j) (v j)
  let T := fun j => ∑ p ∈ S j, (p : ℝ)⁻¹
  let Z := fun j => (∑ p ∈ S j \ D j, (p : ℝ)⁻¹)⁻¹
  let R := ∏ j, Z j * T j
  have ht (j : J) : T j ≠ 0 := harmonic_mass_ne_zero_of_sdiff (S j) (D j) (hD j)
  have hc : R * (∏ j, (T j)⁻¹) = ∏ j, Z j := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    rw [mul_assoc, mul_inv_cancel₀ (ht j), mul_one]
  have h := congrArg ((R : ℂ) * ·) (original_prime_cell_expansion P q a u v c₀ hP hsep f)
  rw [← mul_assoc, ← Complex.ofReal_mul] at h
  change ((R * ∏ j, (T j)⁻¹ : ℝ) : ℂ) * _ = _ at h
  rw [hc] at h
  conv_rhs at h => rw [Finset.mul_sum]
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro x _
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Finset.prod_mul_distrib]
  congr 2
  apply Finset.prod_congr rfl
  intro j _
  exact restored_prime_prior_atom P (S j) (D j) (hD j) (x j)

/-- Restored atoms retain both their actual residue labels and the original
deleted-set normalizer. -/
theorem restored_bulk_residue_expansion {J C : Type*} [Fintype J] [Fintype C]
    (P : Finset ℕ) (M : ℕ) [NeZero M] (u v : J → C → ℝ)
    (c₀ : C × (ZMod M)ˣ)
    (hP : ∀ j, primeCellSupport M (fun c : C × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) ⊆ P)
    (hsep : ∀ j (c d : C × (ZMod M)ˣ), c ≠ d →
      ¬Nat.ModEq M c.2.val.val d.2.val.val ∨ v j c.1 ≤ u j d.1 ∨ v j d.1 ≤ u j c.1)
    (D : J → Finset ℕ)
    (hD : ∀ j, (∑ p ∈ primeCellSupport M (fun c : C × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) \ D j, (p : ℝ)⁻¹) ≠ 0)
    (f : (J → C) → (J → (ZMod M)ˣ) → BulkIntegrand J) :
    let S := fun j => primeCellSupport M (fun c : C × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1)
    let Z := fun j => (∑ p ∈ S j \ D j, (p : ℝ)⁻¹)⁻¹
    let label := fun (x : J → P) j => primeCellLabel M
      (fun c : C × (ZMod M)ˣ => c.2.val.val) (fun c => u j c.1) (fun c => v j c.1) c₀ (x j)
    ((∏ j, Z j : ℝ) : ℂ) * ∑ c : J → C, ∑ z : J → (ZMod M)ˣ,
      ∫ y, f c z y ∂Measure.pi (fun j => primeLogCellMeasure M (z j).val.val (u j (c j)) (v j (c j))) =
    ∑ x : J → P,
      ((∏ j, (if (x j : ℕ) ∈ S j then Z j * (x j : ℝ)⁻¹ else 0) : ℝ) : ℂ) *
        f (fun j => (label x j).1) (fun j => (label x j).2) (fun j => Real.log (x j : ℕ)) := by
  have h := restored_prime_cell_expansion P (fun _ : J => M)
    (fun _ (c : C × (ZMod M)ˣ) => c.2.val.val)
    (fun j c => u j c.1) (fun j c => v j c.1) c₀ hP hsep D hD
    (fun a => f (fun j => (a j).1) (fun j => (a j).2))
  rw [sum_joint_cells_residues] at h
  exact h

end Ostmann

end OAI
