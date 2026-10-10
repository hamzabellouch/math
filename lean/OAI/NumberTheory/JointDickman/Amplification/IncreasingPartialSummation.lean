import OAI.NumberTheory.JointDickman.Amplification.IntegerPartialSummation

namespace OAI

/-! # Increasing weights in finite partial summation -/
namespace JointDickman
open Finset

lemma increasing_weighted_sum_range_bound (g : ℕ → ℂ) (w : ℕ → ℝ)
    {N : ℕ} {D : ℝ} (hD : 0 ≤ D) (hw : ∀ i, 0 ≤ w i)
    (hmono : Monotone w)
    (hpartial : ∀ k ≤ N, ‖∑ i ∈ range k, g i‖ ≤ D) :
    ‖∑ i ∈ range N, w i • g i‖ ≤ 2*D*w N := by
  have htel (M : ℕ) : (∑ i ∈ range M, (w (i+1)-w i)) = w M-w 0 := by
    induction M with
    | zero => simp
    | succ M ih => rw [sum_range_succ, ih]; ring
  cases N with
  | zero => simpa only [range_zero, sum_empty, norm_zero] using
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hD) (hw 0)
  | succ N =>
    rw [sum_range_by_parts]
    simp only [Nat.add_sub_cancel]
    have hterm : ‖w N • (∑ i ∈ range (N+1), g i)‖ ≤ w N*D := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw N)]
      exact mul_le_mul_of_nonneg_left (hpartial _ le_rfl) (hw N)
    have hsum : ‖∑ i ∈ range N, (w (i+1)-w i) • (∑ j ∈ range (i+1), g j)‖ ≤
        (∑ i ∈ range N, (w (i+1)-w i))*D := by
      apply (norm_sum_le _ _).trans
      rw [sum_mul]
      apply sum_le_sum
      intro i hi
      have hii : w i ≤ w (i+1) := hmono (by omega)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hii)]
      exact mul_le_mul_of_nonneg_left (hpartial _ (by have := mem_range.mp hi; omega))
        (sub_nonneg.mpr hii)
    calc
      _ ≤ ‖w N • (∑ i ∈ range (N+1), g i)‖ +
          ‖∑ i ∈ range N, (w (i+1)-w i) • (∑ j ∈ range (i+1), g j)‖ := norm_sub_le _ _
      _ ≤ w N*D+(∑ i ∈ range N, (w (i+1)-w i))*D := add_le_add hterm hsum
      _ ≤ 2*D*w (N+1) := by
        rw [htel]
        nlinarith [hw 0, hmono (show N ≤ N+1 by omega)]

lemma increasing_weighted_sum_Icc_bound (g : ℤ → ℂ) (w : ℤ → ℝ)
    (L R : ℤ) (hLR : L ≤ R) {D : ℝ} (hD : 0 ≤ D)
    (hw : ∀ n, L ≤ n → 0 ≤ w n)
    (hmono : MonotoneOn w (Set.Ici L))
    (hpartial : ∀ V, L ≤ V → V ≤ R → ‖∑ n ∈ Icc L V, g n‖ ≤ D) :
    ‖∑ n ∈ Icc L R, w n • g n‖ ≤ 2*D*w (R+1) := by
  let N := (R+1-L).toNat
  have hN : (N:ℤ) = R+1-L := Int.toNat_of_nonneg (by omega)
  have hR : R = L+(N:ℤ)-1 := by omega
  rw [hR, sum_Icc_int_translate]
  have hh := increasing_weighted_sum_range_bound (fun i => g (L+i))
    (fun i => w (L+i)) hD (fun i => hw _ (by omega))
    (fun i j hij => hmono (by simp) (by simp) (by omega)) (N := N) (by
      intro k hk
      by_cases hk0 : k = 0
      · simpa [hk0] using hD
      · rw [← sum_Icc_int_translate]
        exact hpartial _ (by omega) (by omega))
  convert hh using 1
  congr 2
  omega

end JointDickman

end OAI
