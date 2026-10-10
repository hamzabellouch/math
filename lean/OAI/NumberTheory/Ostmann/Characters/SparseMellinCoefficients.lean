import OAI.NumberTheory.Ostmann.Characters.SparseKernelMeans
import OAI.NumberTheory.Ostmann.Characters.MellinParseval

namespace OAI

/-! # Multiplicative coefficients of the actual sparse additive kernel -/
namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable local instance {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

theorem sum_units_eq_sum_nonzero {p : ℕ} [Fact p.Prime]
    {R : Type*} [AddCommMonoid R] (f : ZMod p → R) :
    (∑ u : (ZMod p)ˣ, f u) = ∑ x ∈ Finset.univ.erase 0, f x := by
  apply Finset.sum_bij (fun (u : (ZMod p)ˣ) _ => (u : ZMod p))
  · intro u _
    exact Finset.mem_erase.mpr ⟨Units.ne_zero u, Finset.mem_univ _⟩
  · intro u _ v _ huv
    exact Units.val_injective huv
  · intro x hx
    exact ⟨Units.mk0 x (Finset.mem_erase.mp hx).1, Finset.mem_univ _, rfl⟩
  · intro _ _
    rfl

theorem sparseAdditiveKernel_total_energy {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t : ℝ) :
    (∑ x, ‖sparseAdditiveKernel E t x‖ ^ 2) = t ^ 2 * E.card / p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hh := additiveFourier_parseval (sparseAdditiveKernel E t)
  simp_rw [sparseAdditiveKernel_fourier, norm_mul, norm_inv, Complex.norm_real,
    Complex.norm_natCast, Real.norm_eq_abs, mul_pow, sq_abs] at hh
  have hs : (∑ a : ZMod p, ‖if a ∈ E then (1 : ℂ) else 0‖ ^ 2) = (E.card : ℝ) := by
    calc
      _ = ∑ a : ZMod p, if a ∈ E then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        split_ifs <;> simp_all
      _ = _ := by simp
  simp_rw [← Finset.mul_sum, hs] at hh
  field_simp at hh
  apply (eq_div_iff hp.ne').mpr
  nlinarith

theorem mellinCoefficient_sq_le_energy {p : ℕ} [Fact p.Prime]
    (f : (ZMod p)ˣ → ℂ) (χ : MulChar (ZMod p) ℂ) :
    ‖mellinCoefficient f χ‖ ^ 2 ≤
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ x, ‖f x‖ ^ 2 := by
  rw [← mellin_parseval]
  exact Finset.single_le_sum (fun ψ _ => sq_nonneg ‖mellinCoefficient f ψ‖) (Finset.mem_univ χ)

/-- Both powers used by the squared truncation have the same square-root
coefficient bound. The proof uses exact Parseval and `|b|<=1`. -/
theorem sparse_power_mellin_sq_le {p : ℕ} [Fact p.Prime]
    (E : Finset (ZMod p)) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (j : ℕ) (hj : j = 1 ∨ j = 2) (χ : MulChar (ZMod p) ℂ) :
    ‖mellinCoefficient (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x ^ j) χ‖ ^ 2 ≤
      2 / p := by
  have hpN := (Fact.out : p.Prime).two_le
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast hpN
  have hp0 : (0 : ℝ) < p := by linarith
  have hcard : (E.card : ℝ) ≤ p := by
    have hh := Finset.card_le_card (Finset.subset_univ E)
    have hh' : E.card ≤ p := by simpa only [Finset.card_univ, ZMod.card] using hh
    exact_mod_cast hh'
  have hnorm (x : ZMod p) : ‖sparseAdditiveKernel E t x‖ ≤ 1 := by
    have hh := sparseAdditiveKernel_norm_le E t ht x
    have hh' : t / p * E.card ≤ 1 := by
      have hc := (div_le_one hp0).mpr hcard
      calc
        _ = t * ((E.card : ℝ) / p) := by ring
        _ ≤ 1 * 1 := mul_le_mul ht1 hc (by positivity) (by norm_num)
        _ = 1 := by ring
    exact hh.trans hh'
  have henergy : (∑ u : (ZMod p)ˣ, ‖sparseAdditiveKernel E t u ^ j‖ ^ 2) ≤ 1 := by
    calc
      _ ≤ ∑ u : (ZMod p)ˣ, ‖sparseAdditiveKernel E t u‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro u _
        rcases hj with rfl | rfl
        · simp
        · rw [norm_pow]
          have hsq : ‖sparseAdditiveKernel E t u‖ ^ 2 ≤ 1 := by
            nlinarith [hnorm u, norm_nonneg (sparseAdditiveKernel E t u)]
          nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg ‖sparseAdditiveKernel E t u‖)]
      _ = ∑ x ∈ Finset.univ.erase 0, ‖sparseAdditiveKernel E t x‖ ^ 2 :=
        sum_units_eq_sum_nonzero (fun x : ZMod p => ‖sparseAdditiveKernel E t x‖ ^ 2)
      _ ≤ ∑ x, ‖sparseAdditiveKernel E t x‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ => sq_nonneg _)
      _ = t ^ 2 * E.card / p := sparseAdditiveKernel_total_energy E t
      _ ≤ 1 := by
        apply (div_le_one hp0).mpr
        have ht2 : t ^ 2 ≤ 1 := by nlinarith
        nlinarith
  have hh := mellinCoefficient_sq_le_energy
    (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x ^ j) χ
  have hc : (Fintype.card (ZMod p)ˣ : ℝ) = (p : ℝ) - 1 := by
    rw [ZMod.card_units, Nat.cast_sub (by omega), Nat.cast_one]
  rw [hc] at hh
  calc
    _ ≤ ((p : ℝ) - 1)⁻¹ * 1 := hh.trans (mul_le_mul_of_nonneg_left henergy (inv_nonneg.mpr (by linarith)))
    _ ≤ 2 / p := by
      rw [mul_one, inv_eq_one_div]
      apply (div_le_div_iff₀ (by linarith) hp0).mpr
      linarith

/-- A convenient non-squared bound for the two local powers. -/
theorem sparse_power_mellin_le {p : ℕ} [Fact p.Prime]
    (E : Finset (ZMod p)) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (j : ℕ) (hj : j = 1 ∨ j = 2) (χ : MulChar (ZMod p) ℂ) :
    ‖mellinCoefficient (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x ^ j) χ‖ ≤
      2 / Real.sqrt (p : ℝ) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hs := Real.sqrt_pos.mpr hp
  have hh := sparse_power_mellin_sq_le E t ht ht1 j hj χ
  have hm := (le_div_iff₀ hp).mp hh
  apply (le_div_iff₀ hs).mpr
  have he : (‖mellinCoefficient (fun x : (ZMod p)ˣ =>
      sparseAdditiveKernel E t x ^ j) χ‖ * Real.sqrt (p : ℝ)) ^ 2 ≤ 2 := by
    rw [mul_pow, Real.sq_sqrt hp.le]
    exact hm
  nlinarith [mul_nonneg (norm_nonneg (mellinCoefficient
    (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x ^ j) χ)) hs.le]

end Ostmann

end OAI
