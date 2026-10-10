import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import OAI.NumberTheory.Ostmann.Construction.FiniteProductPrior

namespace OAI

/-! # Joint approximation of the finite cell and residue distributions

The ideal coordinate masses may be as large as two because the exceptional
real-character multiplier is retained. No independence approximation is
assumed beyond the one-coordinate absolute errors.
-/

namespace Ostmann

open scoped BigOperators

private theorem sum_cons {A R : Type*} [Fintype A] [AddCommMonoid R] {n : ℕ}
    (f : (Fin (n + 1) → A) → R) :
    (∑ x, f x) = ∑ a : A, ∑ x : Fin n → A, f (Fin.cons a x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => A)).sum_comp f, Fintype.sum_prod_type]
  rfl

theorem productPrior_mass_le_two_pow {A : Type*} [Fintype A] {n : ℕ}
    (μ : Fin n → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, ∑ a, μ i a ≤ 2) :
    (∑ x, productPrior μ x) ≤ (2 : ℝ) ^ n := by
  unfold productPrior
  rw [← Fintype.prod_sum]
  calc
    _ ≤ ∏ _i : Fin n, (2 : ℝ) := Finset.prod_le_prod₀
      (fun i _ => Finset.sum_nonneg fun a _ => hμ i a) (fun i _ => hmass i)
    _ = _ := by simp

theorem productPrior_l1_comparison {A : Type*} [Fintype A] (δ : ℝ) (hδ : 0 ≤ δ) :
    ∀ {n : ℕ} (μ ν : Fin n → A → ℝ),
      (∀ i a, 0 ≤ μ i a) → (∀ i a, 0 ≤ ν i a) →
      (∀ i, ∑ a, μ i a ≤ 2) → (∀ i, ∑ a, ν i a ≤ 2) →
      (∀ i, ∑ a, |μ i a - ν i a| ≤ δ) →
      (∑ x, |productPrior μ x - productPrior ν x|) ≤ (n : ℝ) * δ * 2 ^ n := by
  intro n
  induction n with
  | zero => intro μ ν _ _ _ _ _; simp [productPrior]
  | succ n ih =>
    intro μ ν hμ hν hmassμ hmassν hdist
    let μ' := fun i : Fin n => μ i.succ
    let ν' := fun i : Fin n => ν i.succ
    have ht := ih μ' ν' (fun i => hμ i.succ) (fun i => hν i.succ)
      (fun i => hmassμ i.succ) (fun i => hmassν i.succ) (fun i => hdist i.succ)
    have hmν := productPrior_mass_le_two_pow ν' (fun i => hν i.succ) (fun i => hmassν i.succ)
    have hpoint (a : A) (x : Fin n → A) :
        |productPrior μ (Fin.cons a x) - productPrior ν (Fin.cons a x)| ≤
          μ 0 a * |productPrior μ' x - productPrior ν' x| +
            |μ 0 a - ν 0 a| * productPrior ν' x := by
      rw [productPrior_cons, productPrior_cons]
      have he : μ 0 a * productPrior μ' x - ν 0 a * productPrior ν' x =
          μ 0 a * (productPrior μ' x - productPrior ν' x) +
            (μ 0 a - ν 0 a) * productPrior ν' x := by ring
      rw [he]
      refine (abs_add_le _ _).trans_eq ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (hμ 0 a),
        abs_of_nonneg (productPrior_nonneg ν' (fun i => hν i.succ) x)]
    rw [sum_cons]
    calc
      _ ≤ ∑ a : A, ∑ x : Fin n → A,
          (μ 0 a * |productPrior μ' x - productPrior ν' x| +
            |μ 0 a - ν 0 a| * productPrior ν' x) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun x _ => hpoint a x
      _ = (∑ a, μ 0 a) * (∑ x, |productPrior μ' x - productPrior ν' x|) +
          (∑ a, |μ 0 a - ν 0 a|) * (∑ x, productPrior ν' x) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      _ ≤ 2 * ((n : ℝ) * δ * 2 ^ n) + δ * 2 ^ n := by
        exact add_le_add
          (mul_le_mul (hmassμ 0) ht (Finset.sum_nonneg fun x _ => abs_nonneg _) (by norm_num))
          (mul_le_mul (hdist 0) hmν
            (Finset.sum_nonneg fun x _ => productPrior_nonneg ν' (fun i => hν i.succ) x) hδ)
      _ ≤ ((n + 1 : ℕ) : ℝ) * δ * 2 ^ (n + 1) := by
        rw [Nat.cast_add, Nat.cast_one, pow_succ]
        nlinarith [show 0 ≤ δ * (2 : ℝ) ^ n by positivity]

/-- The joint coordinate replacement for a bounded signed spectator and
smooth amplitude. The exceptional-character factors remain in the priors. -/
theorem weighted_productPrior_comparison {A : Type*} [Fintype A] {n : ℕ}
    (μ ν : Fin n → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hν : ∀ i a, 0 ≤ ν i a)
    (hmassμ : ∀ i, ∑ a, μ i a ≤ 2) (hmassν : ∀ i, ∑ a, ν i a ≤ 2)
    (δ B : ℝ) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hdist : ∀ i, ∑ a, |μ i a - ν i a| ≤ δ)
    (F : (Fin n → A) → ℂ) (hF : ∀ x, ‖F x‖ ≤ B) :
    ‖(∑ x, (productPrior μ x : ℂ) * F x) - (∑ x, (productPrior ν x : ℂ) * F x)‖ ≤
      B * n * δ * 2 ^ n := by
  have heq : (∑ x, (productPrior μ x : ℂ) * F x) -
      (∑ x, (productPrior ν x : ℂ) * F x) =
      ∑ x, ((productPrior μ x - productPrior ν x : ℝ) : ℂ) * F x := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [Complex.ofReal_sub, sub_mul]
  rw [heq]
  calc
    _ ≤ ∑ x, ‖((productPrior μ x - productPrior ν x : ℝ) : ℂ) * F x‖ := norm_sum_le _ _
    _ = ∑ x, |productPrior μ x - productPrior ν x| * ‖F x‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ x, |productPrior μ x - productPrior ν x| * B :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hF x) (abs_nonneg _)
    _ = (∑ x, |productPrior μ x - productPrior ν x|) * B := (Finset.sum_mul _ _ _).symm
    _ ≤ ((n : ℝ) * δ * 2 ^ n) * B := mul_le_mul_of_nonneg_right
      (productPrior_l1_comparison δ hδ μ ν hμ hν hmassμ hmassν hdist) hB
    _ = _ := by ring

/-- Freezing the smooth factor in each joint box only costs its uniform
variation times the total mass. -/
theorem weighted_productPrior_variation {A : Type*} [Fintype A] {n : ℕ}
    (μ : Fin n → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, ∑ a, μ i a ≤ 2)
    (F G : (Fin n → A) → ℂ) (η : ℝ) (hη : 0 ≤ η) (hFG : ∀ x, ‖F x - G x‖ ≤ η) :
    ‖(∑ x, (productPrior μ x : ℂ) * F x) - (∑ x, (productPrior μ x : ℂ) * G x)‖ ≤
      η * 2 ^ n := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ x, ‖(productPrior μ x : ℂ) * (F x - G x)‖ := norm_sum_le _ _
    _ = ∑ x, productPrior μ x * ‖F x - G x‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (productPrior_nonneg μ hμ _)]
    _ ≤ ∑ x, productPrior μ x * η := Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_left (hFG x) (productPrior_nonneg μ hμ x)
    _ = (∑ x, productPrior μ x) * η := (Finset.sum_mul _ _ _).symm
    _ ≤ (2 : ℝ) ^ n * η := mul_le_mul_of_nonneg_right (productPrior_mass_le_two_pow μ hμ hmass) hη
    _ = _ := mul_comm _ _

end Ostmann

end OAI
