import OAI.NumberTheory.Ostmann.Tree.SignedCycleBound

namespace OAI

/-! # Independent held-leaf averaging in the cycle projection -/

namespace Ostmann

open scoped BigOperators

theorem uniform_product_average {I H : Type*} [Fintype I] [DecidableEq I] [Fintype H]
    (f : I → H → ℝ) :
    ((Fintype.card H : ℝ) ^ Fintype.card I)⁻¹ * (∑ h : I → H, ∏ i : I, f i (h i)) =
      ∏ i : I, (Fintype.card H : ℝ)⁻¹ * ∑ h : H, f i h := by
  rw [← Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, inv_pow]

noncomputable local instance heldCycleFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance heldCycleDecidableEq {p : ℕ} :
    DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

/-- Fubini and the cycle-character relation remain exact after exposing the
independent held coordinates in every affected quartet. -/
theorem held_cycle_product_energy {p : ℕ} [Fact p.Prime]
    {I H : Type*} [Fintype I] [DecidableEq I] [Fintype H]
    (f : I → H → (ZMod p)ˣ → ℂ) (sign : I → ℤ) :
    ((Fintype.card H : ℝ) ^ Fintype.card I)⁻¹ * (∑ h : I → H,
      ((Fintype.card (ZMod p)ˣ : ℝ) ^ Fintype.card I)⁻¹ *
        ∑ m : I → (ZMod p)ˣ,
          ‖cycleAverage sign (fun m => ∏ i : I, f i (h i) (m i)) m‖ ^ 2) =
    ∑ ρ : I → MulChar (ZMod p) ℂ,
      if (∏ i : I, (ρ i) ^ sign i) = 1 then
        ∏ i : I, (Fintype.card H : ℝ)⁻¹ * ∑ h : H, ‖mellinCoefficient (f i h) (ρ i)‖ ^ 2
      else 0 := by
  classical
  simp_rw [cycleAverage_product_energy]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ρ _
  by_cases hr : (∏ i : I, (ρ i) ^ sign i) = 1
  · simp only [hr, ite_true]
    rw [← Finset.mul_sum]
    simpa only [Finset.mul_sum] using
      uniform_product_average (fun i h => ‖mellinCoefficient (f i h) (ρ i)‖ ^ 2)
  · simp only [hr, ite_false, mul_zero, Finset.sum_const_zero]

theorem held_cycle_product_energy_le {p : ℕ} [Fact p.Prime]
    {I H : Type*} [Fintype I] [DecidableEq I] [Fintype H]
    (f : I → H → (ZMod p)ˣ → ℂ) (sign : I → ℤ)
    (B : I → MulChar (ZMod p) ℂ → ℝ)
    (hcoeff : ∀ i χ, (Fintype.card H : ℝ)⁻¹ *
      (∑ h : H, ‖mellinCoefficient (f i h) χ‖ ^ 2) ≤ B i χ) :
    ((Fintype.card H : ℝ) ^ Fintype.card I)⁻¹ * (∑ h : I → H,
      ((Fintype.card (ZMod p)ˣ : ℝ) ^ Fintype.card I)⁻¹ *
        ∑ m : I → (ZMod p)ˣ,
          ‖cycleAverage sign (fun m => ∏ i : I, f i (h i) (m i)) m‖ ^ 2) ≤
    ∑ ρ : I → MulChar (ZMod p) ℂ,
      if (∏ i : I, (ρ i) ^ sign i) = 1 then ∏ i : I, B i (ρ i) else 0 := by
  classical
  rw [held_cycle_product_energy]
  apply Finset.sum_le_sum
  intro ρ _
  split_ifs
  · exact Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => hcoeff i (ρ i))
  · exact le_rfl

/-- Averaging independent quartet arguments factorizes each surviving
character term before a single character is eliminated by the cycle. -/
theorem cycle_majorant_average {I G Y : Type*} [Fintype I] [DecidableEq I] [Fintype G] [Fintype Y]
    [CommGroup G] [DecidableEq G] (B : I → G → Y → ℝ) (sign : I → ℤ) :
    ((Fintype.card Y : ℝ) ^ Fintype.card I)⁻¹ * (∑ y : I → Y,
      ∑ ρ : I → G, if (∏ i : I, (ρ i) ^ sign i) = 1 then ∏ i : I, B i (ρ i) (y i) else 0) =
    ∑ ρ : I → G, if (∏ i : I, (ρ i) ^ sign i) = 1 then
      ∏ i : I, (Fintype.card Y : ℝ)⁻¹ * ∑ y : Y, B i (ρ i) y else 0 := by
  classical
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ρ _
  by_cases hr : (∏ i : I, (ρ i) ^ sign i) = 1
  · simp only [hr, ite_true]
    rw [← Finset.mul_sum]
    simpa only [Finset.mul_sum] using uniform_product_average (fun i y => B i (ρ i) y)
  · simp only [hr, ite_false, mul_zero, Finset.sum_const_zero]

theorem cycle_majorant_average_le {I G Y : Type*} [Fintype I] [DecidableEq I]
    [Fintype G] [Fintype Y] [CommGroup G] [DecidableEq G]
    (B : I → G → Y → ℝ) (sign : I → ℤ) (i : I) (hi : sign i = 1 ∨ sign i = -1)
    (M : ℝ) (H : I → ℝ) (hM : 0 ≤ M)
    (hB : ∀ j χ y, 0 ≤ B j χ y)
    (hsmall : ∀ χ, (Fintype.card Y : ℝ)⁻¹ * ∑ y : Y, B i χ y ≤ M)
    (hmass : ∀ j, (∑ χ : G, (Fintype.card Y : ℝ)⁻¹ * ∑ y : Y, B j χ y) ≤ H j) :
    ((Fintype.card Y : ℝ) ^ Fintype.card I)⁻¹ * (∑ y : I → Y,
      ∑ ρ : I → G, if (∏ j : I, (ρ j) ^ sign j) = 1 then ∏ j : I, B j (ρ j) (y j) else 0) ≤
      M * ∏ j : {j : I // j ≠ i}, H j.1 := by
  classical
  rw [cycle_majorant_average]
  apply (signedCycleCoefficient_sum_le
    (fun j χ => (Fintype.card Y : ℝ)⁻¹ * ∑ y : Y, B j χ y) sign i hi M
    (fun j χ => mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => hB j χ y)) hsmall).trans
  apply mul_le_mul_of_nonneg_left _ hM
  exact Finset.prod_le_prod₀ (fun j _ => Finset.sum_nonneg fun χ _ =>
    mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => hB j.1 χ y)) (fun j _ => hmass j.1)

end Ostmann

end OAI
