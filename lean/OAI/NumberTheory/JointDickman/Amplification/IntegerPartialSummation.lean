import OAI.NumberTheory.JointDickman.Amplification.MonotonePartialSummation

namespace OAI

/-! # Decreasing weights on integer intervals -/
namespace JointDickman
open Finset

lemma sum_Icc_int_translate {E : Type*} [AddCommMonoid E] (g : ℤ → E)
    (L : ℤ) (N : ℕ) :
    ∑ n ∈ Icc L (L+(N:ℤ)-1), g n = ∑ i ∈ range N, g (L+i) := by
  rw [Int.Icc_eq_finset_map, sum_map]
  simp only [sub_add_cancel, add_sub_cancel_left, Int.toNat_natCast]
  rfl

lemma monotone_weighted_sum_Icc_bound (g : ℤ → ℂ) (w : ℤ → ℝ)
    (L R : ℤ) {D : ℝ} (hD : 0 ≤ D)
    (hw : ∀ n, L ≤ n → 0 ≤ w n)
    (hanti : AntitoneOn w (Set.Ici L))
    (hpartial : ∀ V, L ≤ V → V ≤ R → ‖∑ n ∈ Icc L V, g n‖ ≤ D) :
    ‖∑ n ∈ Icc L R, w n • g n‖ ≤ D*w L := by
  by_cases hLR : L ≤ R
  · let N := (R+1-L).toNat
    have hN : (N:ℤ) = R+1-L := Int.toNat_of_nonneg (by omega)
    have hR : R = L+(N:ℤ)-1 := by omega
    rw [hR, sum_Icc_int_translate]
    have hh := monotone_weighted_sum_range_bound (fun i => g (L+i))
      (fun i => w (L+i)) hD (fun i => hw _ (by omega))
      (fun i j hij => hanti (by simp) (by simp) (by omega))
      (N := N) (by
        intro k hk
        by_cases hk0 : k = 0
        · simpa [hk0] using hD
        · rw [←sum_Icc_int_translate]
          exact hpartial _ (by omega) (by omega))
    simpa only [Nat.cast_zero, add_zero] using hh
  · simp only [Icc_eq_empty_of_lt (lt_of_not_ge hLR), sum_empty, norm_zero]
    exact mul_nonneg hD (hw L le_rfl)

lemma rpow_weighted_sum_Icc_bound (g : ℤ → ℂ) (L R : ℤ)
    {D σ : ℝ} (hL : 0 < L) (hD : 0 ≤ D) (hσ : 0 ≤ σ)
    (hpartial : ∀ V, L ≤ V → V ≤ R → ‖∑ n ∈ Icc L V, g n‖ ≤ D) :
    ‖∑ n ∈ Icc L R, (((n:ℝ)^(-σ):ℝ):ℂ)*g n‖ ≤ D*(L:ℝ)^(-σ) := by
  have hh := monotone_weighted_sum_Icc_bound g (fun n => (n:ℝ)^(-σ)) L R hD
    (fun n hn => Real.rpow_nonneg (by exact_mod_cast (hL.le.trans hn)) _)
    (by
      intro i hi j hj hij
      apply Real.rpow_le_rpow_of_nonpos
      · exact_mod_cast hL.trans_le hi
      · exact_mod_cast hij
      · linarith) hpartial
  simpa only [Complex.real_smul] using hh

end JointDickman

end OAI
