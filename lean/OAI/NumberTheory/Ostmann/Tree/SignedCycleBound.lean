import Mathlib.Logic.Equiv.Prod
import OAI.NumberTheory.Ostmann.Characters.ProductMellinParseval
import OAI.NumberTheory.Ostmann.Characters.CycleCoefficient

namespace OAI

/-! # Quantitative coefficient bound for a signed cycle -/

namespace Ostmann

open scoped BigOperators

theorem sum_funSplitAt {I G R : Type*} [Fintype I] [DecidableEq I] [Fintype G]
    [AddCommMonoid R] (i : I) (f : G → ({j : I // j ≠ i} → G) → R) :
    (∑ ρ : I → G, f (ρ i) (fun j => ρ j.1)) =
      ∑ a : G, ∑ τ : {j : I // j ≠ i} → G, f a τ := by
  have h := (Equiv.funSplitAt i G).sum_comp (fun x => f x.1 x.2)
  change (∑ ρ : I → G, f (ρ i) (fun j => ρ j.1)) = _ at h
  simpa only [Fintype.sum_prod_type] using h

/-- Once a cycle index has sign `1` or `-1`, its character is determined by all the others. -/
theorem signedCycleCoefficient_sum_le {I G : Type*} [Fintype I] [DecidableEq I]
    [CommGroup G] [Fintype G] [DecidableEq G]
    (b : I → G → ℝ) (sign : I → ℤ) (i : I)
    (hi : sign i = 1 ∨ sign i = -1) (S : ℝ)
    (hb : ∀ j a, 0 ≤ b j a) (hS : ∀ a, b i a ≤ S) :
    (∑ ρ : I → G, if (∏ j : I, (ρ j) ^ sign j) = 1 then ∏ j : I, b j (ρ j) else 0) ≤
      S * ∏ j : {j : I // j ≠ i}, ∑ a : G, b j.1 a := by
  classical
  have hproduct (ρ : I → G) :
      (∏ j : I, (ρ j) ^ sign j) = (ρ i) ^ sign i *
        ∏ j : {j : I // j ≠ i}, (ρ j.1) ^ sign j.1 :=
    Fintype.prod_eq_mul_prod_subtype_ne _ i
  have hweight (ρ : I → G) :
      (∏ j : I, b j (ρ j)) = b i (ρ i) * ∏ j : {j : I // j ≠ i}, b j.1 (ρ j.1) :=
    Fintype.prod_eq_mul_prod_subtype_ne _ i
  simp_rw [hproduct, hweight]
  rw [sum_funSplitAt i (fun a τ =>
    if a ^ sign i * (∏ j : {j : I // j ≠ i}, (τ j) ^ sign j.1) = 1 then
      b i a * (∏ j : {j : I // j ≠ i}, b j.1 (τ j)) else 0), Finset.sum_comm]
  have hinner (τ : {j : I // j ≠ i} → G) :
      (∑ a : G, if a ^ sign i * (∏ j, (τ j) ^ sign j.1) = 1 then
        b i a * (∏ j, b j.1 (τ j)) else 0) ≤ S * ∏ j, b j.1 (τ j) := by
    rcases hi with hi | hi
    · simp only [hi, zpow_one, mul_eq_one_iff_eq_inv]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      exact mul_le_mul_of_nonneg_right (hS _) (Finset.prod_nonneg fun j _ => hb j.1 _)
    · simp only [hi, zpow_neg_one, inv_mul_eq_one]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      exact mul_le_mul_of_nonneg_right (hS _) (Finset.prod_nonneg fun j _ => hb j.1 _)
  calc
    _ ≤ ∑ τ : {j : I // j ≠ i} → G, S * ∏ j, b j.1 (τ j) :=
      Finset.sum_le_sum fun τ _ => hinner τ
    _ = _ := by rw [← Finset.mul_sum, Fintype.prod_sum]

noncomputable local instance signedCycleFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

/-- The quantitative form of the final cycle-projection step. -/
theorem cycleAverage_product_energy_le {p : ℕ} [Fact p.Prime]
    {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → (ZMod p)ˣ → ℂ) (sign : I → ℤ) (i : I)
    (hi : sign i = 1 ∨ sign i = -1) (S : ℝ)
    (hS : ∀ χ : MulChar (ZMod p) ℂ, ‖mellinCoefficient (f i) χ‖ ^ 2 ≤ S) :
    ((Fintype.card (ZMod p)ˣ : ℝ) ^ Fintype.card I)⁻¹ *
      (∑ m : I → (ZMod p)ˣ, ‖cycleAverage sign (fun m => ∏ j : I, f j (m j)) m‖ ^ 2) ≤
      S * ∏ j : {j : I // j ≠ i},
        (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ t : (ZMod p)ˣ, ‖f j.1 t‖ ^ 2 := by
  classical
  rw [cycleAverage_product_energy]
  have h := signedCycleCoefficient_sum_le (fun j χ => ‖mellinCoefficient (f j) χ‖ ^ 2)
    sign i hi S (fun _ _ => sq_nonneg _) hS
  convert h using 1
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  exact (mellin_parseval (f j.1)).symm

end Ostmann

end OAI
