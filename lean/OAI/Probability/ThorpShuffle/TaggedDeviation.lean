import OAI.Probability.ThorpShuffle.ConditionalLaw

namespace OAI

universe uΩ uα uι

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

theorem mean_sub {Ω : Type uΩ} [Fintype Ω] (f g : Ω → ℝ) :
    mean (fun ω => f ω - g ω) = mean f - mean g := by
  simp only [mean, Finset.sum_sub_distrib, sub_div]

theorem abs_mean_le {Ω : Type uΩ} [Fintype Ω] (f : Ω → ℝ) :
    |mean f| ≤ mean (fun ω => |f ω|) := by
  unfold mean
  rw [abs_div, abs_of_nonneg (Nat.cast_nonneg (Fintype.card Ω) : (0 : ℝ) ≤ Fintype.card Ω)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

theorem mean_sq_le {Ω : Type uΩ} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    mean f ^ 2 ≤ mean (fun ω => f ω ^ 2) := by
  have h := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ f (fun _ => (1 : ℝ))
  simpa only [mul_one, one_pow, Finset.expect_const (Finset.univ_nonempty),
    Finset.expect_eq_sum_div_card, Finset.card_univ, mean] using h

theorem mean_l1_le_sqrt {Ω : Type uΩ} {α : Type uα} [Fintype Ω] [Nonempty Ω] [Fintype α]
    (w : Ω → α → ℝ) :
    mean (fun ω => ∑ x, |w ω x|) ≤
      Real.sqrt ((Fintype.card α : ℝ) * mean (fun ω => ∑ x, w ω x ^ 2)) := by
  apply Real.le_sqrt_of_sq_le
  calc
    _ ≤ mean (fun ω => (∑ x, |w ω x|) ^ 2) := mean_sq_le _
    _ ≤ mean (fun ω => (Fintype.card α : ℝ) * ∑ x, w ω x ^ 2) := by
      apply mean_le_mean
      intro ω
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : α => (1 : ℝ)) (fun x => |w ω x|)
      simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, sq_abs] using h
    _ = _ := mean_const_mul _ _

theorem mean_weighted_test_le {Ω : Type uΩ} {α : Type uα} [Fintype Ω] [Nonempty Ω] [Fintype α]
    (w f : Ω → α → ℝ) (hf : ∀ ω x, |f ω x| ≤ 1) :
    |mean (fun ω => ∑ x, w ω x * f ω x)| ≤
      Real.sqrt ((Fintype.card α : ℝ) * mean (fun ω => ∑ x, w ω x ^ 2)) := by
  calc
    _ ≤ mean (fun ω => |∑ x, w ω x * f ω x|) := abs_mean_le _
    _ ≤ mean (fun ω => ∑ x, |w ω x|) := by
      apply mean_le_mean
      intro ω
      calc
        _ ≤ ∑ x, |w ω x * f ω x| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := Finset.sum_le_sum (fun x _ => by
          rw [abs_mul]
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (hf ω x) (abs_nonneg _))
    _ ≤ _ := mean_l1_le_sqrt w

theorem tagged_deviation_bound {ι : Type uι} (d : ℕ)
    (B : Position (d + 1) → Bool) (tag : Position (d + 1)) (ht : B tag = true)
    (e : ι → Position (d + 1)) (he : ∀ i, B (e i) = false)
    (t : ℕ) (f : (ι → Position (d + 1)) → Position (d + 1) → ℝ)
    (hf : ∀ e' y, |f e' y| ≤ 1) :
    |mean (fun ω : History (d + 1) t =>
      f ((run (d + 1) t ω) ∘ e) (run (d + 1) t ω tag) -
        (1 / (freeCount B : ℝ)) *
          (∑ y, if B ((run (d + 1) t ω).symm y) then f ((run (d + 1) t ω) ∘ e) y else 0))| ≤
    Real.sqrt ((Fintype.card (Position (d + 1)) : ℝ) *
      expectedEnergy d (initialState (d + 1) B tag ht) t) := by
  rw [tagged_deviation_identity d B tag ht e he]
  exact mean_weighted_test_le _ _ (fun ω y => hf _ y)

end Conditional

end Thorp

end

end OAI
