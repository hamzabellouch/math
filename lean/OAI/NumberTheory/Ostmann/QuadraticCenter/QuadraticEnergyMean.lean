import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticSmallSumEnergy

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators ComplexConjugate

theorem sum_zmod_eq_sum_range {A : Type*} [AddCommMonoid A] {d : ℕ} [NeZero d]
    (f : ZMod d → A) : (∑ z, f z) = ∑ n ∈ Finset.range d, f (n : ZMod d) := by
  classical
  apply Finset.sum_bij (fun z _ => z.val)
  · intro z hz
    exact Finset.mem_range.mpr (ZMod.val_lt z)
  · intro z hz y hy heq
    exact ZMod.val_injective d heq
  · intro n hn
    refine ⟨(n : ZMod d), Finset.mem_univ _, ?_⟩
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hn)]
  · intro z hz
    simp only [ZMod.natCast_zmod_val]

theorem sum_range_multiple_cast {d : ℕ} [NeZero d] (f : ZMod d → ℝ) (k : ℕ) :
    (∑ n ∈ Finset.range (k * d), f (n : ZMod d)) = (k : ℝ) * ∑ z, f z := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
      rw [← sum_zmod_eq_sum_range]
      push_cast
      ring

theorem sum_zmod_castHom {L d : ℕ} [NeZero L] [NeZero d] (hd : d ∣ L)
    (f : ZMod d → ℝ) :
    (∑ z : ZMod L, f (ZMod.castHom hd (ZMod d) z)) = (L / d : ℕ) * ∑ y, f y := by
  rw [sum_zmod_eq_sum_range]
  simp only [map_natCast]
  conv_lhs => rw [← Nat.div_mul_cancel hd]
  exact sum_range_multiple_cast f (L / d)

theorem centeredProductTransform_scalar_energy_le {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hp : ∀ i, (p i).Prime)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (A : ∀ i, Finset (ZMod (p i))) (c : ZMod (∏ i, p i)) :
    (∑ z, ‖centeredProductTransform p hcop A (c * z)‖ ^ 2) ≤ (∏ i, p i : ℕ) := by
  classical
  by_cases hc : IsUnit c
  · obtain ⟨u, rfl⟩ := hc
    simp only [centeredProductTransform, unitaryDFT_unit_dilation]
    rw [Supply.unitaryDFT_parseval]
    calc
      _ ≤ ∑ _z : ZMod (∏ i, p i), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro z hz
        have hh := norm_centeredProduct_le_one p hcop A
          (((u⁻¹ : (ZMod (∏ i, p i))ˣ) : ZMod (∏ i, p i)) * z)
        have hn := norm_nonneg (centeredProduct p hcop A
          (((u⁻¹ : (ZMod (∏ i, p i))ˣ) : ZMod (∏ i, p i)) * z))
        nlinarith
      _ = _ := by simp
  · simp_rw [centeredProductTransform_mul_eq_zero_of_not_isUnit p hp hcop A c _ hc,
      norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
    positivity

theorem centeredProductTransform_lifted_energy_le {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hp : ∀ i, (p i).Prime)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (A : ∀ i, Finset (ZMod (p i))) (c : ZMod (∏ i, p i))
    {L : ℕ} [NeZero L] (hd : (∏ i, p i) ∣ L) :
    (∑ z : ZMod L, ‖centeredProductTransform p hcop A
      (c * ZMod.castHom hd (ZMod (∏ i, p i)) z)‖ ^ 2) ≤ L := by
  rw [sum_zmod_castHom hd (fun z => ‖centeredProductTransform p hcop A (c * z)‖ ^ 2)]
  calc
    _ ≤ ((L / (∏ i, p i) : ℕ) : ℝ) * (∏ i, p i : ℕ) :=
      mul_le_mul_of_nonneg_left (centeredProductTransform_scalar_energy_le p hp hcop A c)
        (Nat.cast_nonneg _)
    _ = _ := by exact_mod_cast Nat.div_mul_cancel hd

theorem centered_transform_product_period_l1_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℕ) (r : κ → ℕ) [∀ i, NeZero (p i)] [∀ j, NeZero (r j)]
    [NeZero (∏ i, p i)] [NeZero (∏ j, r j)]
    (hp : ∀ i, (p i).Prime) (hr : ∀ j, (r j).Prime)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (hcor : Pairwise (fun i j => (r i).Coprime (r j)))
    (A : ∀ i, Finset (ZMod (p i))) (B : ∀ j, Finset (ZMod (r j)))
    (c : ZMod (∏ i, p i)) (c' : ZMod (∏ j, r j))
    {L : ℕ} [NeZero L] (hd : (∏ i, p i) ∣ L) (he : (∏ j, r j) ∣ L) :
    (∑ z : ZMod L, ‖centeredProductTransform p hcop A
      (c * ZMod.castHom hd (ZMod (∏ i, p i)) z) *
      conj (centeredProductTransform r hcor B
        (c' * ZMod.castHom he (ZMod (∏ j, r j)) z))‖) ≤ L := by
  let f : ZMod L → ℝ := fun z => ‖centeredProductTransform p hcop A
    (c * ZMod.castHom hd (ZMod (∏ i, p i)) z)‖
  let g : ZMod L → ℝ := fun z => ‖centeredProductTransform r hcor B
    (c' * ZMod.castHom he (ZMod (∏ j, r j)) z)‖
  simp only [norm_mul, Complex.norm_conj]
  change (∑ z, f z * g z) ≤ (L : ℝ)
  apply le_of_sq_le_sq _ (Nat.cast_nonneg _)
  calc
    _ ≤ (∑ z, f z ^ 2) * ∑ z, g z ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ f g
    _ ≤ (L : ℝ) * L := mul_le_mul
      (centeredProductTransform_lifted_energy_le p hp hcop A c hd)
      (centeredProductTransform_lifted_energy_le r hr hcor B c' he)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)
    _ = _ := by ring

end Ostmann.QuadraticCenter

end

end OAI
