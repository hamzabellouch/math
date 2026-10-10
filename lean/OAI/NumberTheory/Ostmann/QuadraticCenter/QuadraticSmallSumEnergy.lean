import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticSmallSumFibers
import OAI.NumberTheory.Ostmann.Supply.FiniteParseval

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem sum_comp_le_fiber_bound {α β : Type*} [Fintype β] [DecidableEq β]
    (S : Finset α) (f : α → β) (g : β → ℝ) (B : ℝ)
    (hg : ∀ b, 0 ≤ g b)
    (hf : ∀ b, ((S.filter (fun a => f a = b)).card : ℝ) ≤ B) :
    ∑ a ∈ S, g (f a) ≤ B * ∑ b, g b := by
  classical
  rw [← Finset.sum_fiberwise' S f g, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (hf b) (hg b)

theorem centeredProductTransform_energy_le {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) :
    ∑ z, ‖centeredProductTransform p hcop S z‖ ^ 2 ≤ (∏ i, p i : ℕ) := by
  unfold centeredProductTransform
  rw [Supply.unitaryDFT_parseval]
  calc
    _ ≤ ∑ _z : ZMod (∏ i, p i), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro z _
      have h := norm_centeredProduct_le_one p hcop S z
      have hn := norm_nonneg (centeredProduct p hcop S z)
      nlinarith
    _ = _ := by simp

theorem centeredProductTransform_square_energy_le {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hp : ∀ i, (p i).Prime)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (c : ZMod (∏ i, p i)) :
    ∑ w, ‖centeredProductTransform p hcop S (c * w ^ 2)‖ ^ 2 ≤
      (2 : ℝ) ^ Fintype.card ι * (∏ i, p i : ℕ) := by
  classical
  by_cases hc : IsUnit c
  · calc
      _ ≤ (2 : ℝ) ^ Fintype.card ι * ∑ z, ‖centeredProductTransform p hcop S z‖ ^ 2 := by
        apply sum_comp_le_fiber_bound Finset.univ (fun w => c * w ^ 2)
          (fun z => ‖centeredProductTransform p hcop S z‖ ^ 2)
          ((2 : ℝ) ^ Fintype.card ι) (fun _ => sq_nonneg _)
        intro b
        exact_mod_cast prime_product_scaled_square_fiber_card_le p hp hcop c b hc
      _ ≤ _ := mul_le_mul_of_nonneg_left (centeredProductTransform_energy_le p hcop S)
        (by positivity)
  · simp_rw [centeredProductTransform_mul_eq_zero_of_not_isUnit p hp hcop S c _ hc,
      norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
    positivity

theorem centeredProductTransform_square_l1_le {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hp : ∀ i, (p i).Prime)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (c : ZMod (∏ i, p i)) :
    ∑ w, ‖centeredProductTransform p hcop S (c * w ^ 2)‖ ≤
      (∏ i, p i : ℕ) * Real.sqrt ((2 : ℝ) ^ Fintype.card ι) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod (∏ i, p i)))
    (fun _ => (1 : ℝ)) (fun w => ‖centeredProductTransform p hcop S (c * w ^ 2)‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_univ, ZMod.card] at hcs
  have he := centeredProductTransform_square_energy_le p hp hcop S c
  have he' := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (∏ i, p i) : (0 : ℝ) ≤ _)
  have hs := Real.sq_sqrt (show 0 ≤ (2 : ℝ) ^ Fintype.card ι by positivity)
  have hnon : 0 ≤ (∏ i, p i : ℕ) * Real.sqrt ((2 : ℝ) ^ Fintype.card ι) := by positivity
  apply le_of_sq_le_sq _ hnon
  calc
    _ ≤ _ := hcs.trans he'
    _ = _ := by rw [mul_pow, hs]; ring

end Ostmann.QuadraticCenter

end

end OAI
