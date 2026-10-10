import OAI.Probability.CriticalPercolation.Entropy.Divergence

namespace OAI

namespace Percolation.BenjaminiSchramm

open CriticalPercolation.FiniteEntropy

theorem exp_neg_one_le_half : Real.exp (-1) ≤ 1 / 2 := by
  have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (1 : ℝ))
    (Real.exp_pos (-1)).le
  have he : Real.exp (1 : ℝ) * Real.exp (-1) = 1 := by rw [←Real.exp_add]; norm_num
  rw [he] at hh
  norm_num only [one_add_one_eq_two] at hh
  linarith

theorem event_mass_le_two_add_divergence
    {X : Type*} [Fintype X] (P Q : X → ℝ) (A : X → Bool)
    (hP : ∀ x, 0 ≤ P x) (hQ : ∀ x, 0 ≤ Q x)
    (hPsum : ∑ x, P x = 1) (hQsum : ∑ x, Q x = 1)
    (hs : ∀ x, 0 < P x → 0 < Q x) :
    (∑ x, if A x then Q x else 0) ≤
      2 * (∑ x, if A x then P x else 0) + 2 * divergence P Q := by
  let g : X → ℝ := fun x => if A x then -1 else 0
  let a : ℝ := ∑ x, if A x then P x else 0
  let b : ℝ := ∑ x, if A x then Q x else 0
  have hb : 0 ≤ b := Finset.sum_nonneg (fun x _ => by split_ifs; exact hQ x; rfl)
  have htest : (∑ x, P x * g x) = -a := by
    dsimp only [a]
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    dsimp [g]
    split_ifs <;> ring
  have hZ : (∑ x, Q x * Real.exp (g x)) = 1 - (1 - Real.exp (-1)) * b := by
    dsimp only [b]
    calc
      _ = (∑ x, Q x) - (1 - Real.exp (-1)) * (∑ x, if A x then Q x else 0) := by
        rw [Finset.mul_sum,←Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x _
        dsimp [g]
        split_ifs
        · ring
        · rw [Real.exp_zero]
          ring
      _ = _ := by rw [hQsum]
  have hZpos := normalizer_pos P Q hP hQ hPsum hs g
  have hlog := Real.log_le_sub_one_of_pos hZpos
  have hentropy := entropy_inequality P Q hP hQ hPsum hs g
  rw [htest,hZ] at hentropy
  rw [hZ] at hlog
  have hh := mul_le_mul_of_nonneg_right exp_neg_one_le_half hb
  change b ≤ 2 * a + 2 * divergence P Q
  linarith

theorem divergence_mul
    {X : Type*} [Fintype X] (P Q : X → ℝ)
    (hP : ∀ x, 0 < P x) (hQ : ∀ x, 0 < Q x) (hPsum : ∑ x, P x = 1)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    divergence (fun x => a * P x) (fun x => b * Q x) =
      a * divergence P Q + a * Real.log (a / b) := by
  have ht (x : X) : (a * P x) * Real.log ((a * P x) / (b * Q x)) =
      a * (P x * Real.log (P x / Q x)) + (a * Real.log (a / b)) * P x := by
    rw [show (a * P x) / (b * Q x) = (a / b) * (P x / Q x) by ring,
      Real.log_mul (div_ne_zero ha.ne' hb.ne') (div_ne_zero (hP x).ne' (hQ x).ne')]
    ring
  simp only [divergence,ht,Finset.sum_add_distrib,←Finset.mul_sum,hPsum,mul_one]

end Percolation.BenjaminiSchramm

end OAI
