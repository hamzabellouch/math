import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.DyadicCorrectionProgress

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open scoped BigOperators

lemma dyadic_reciprocal (C s : ℝ) (j : ℕ) :
    C/(s*2^j) = (C/s)*(1/2:ℝ)^j := by
  rw [div_pow,one_pow]
  ring

lemma sum_dyadic_square_le {s : ℝ} (hs : 0 ≤ s) (N : ℕ) :
    ∑ j ∈ Finset.range N, (s*2^j)^2 ≤ (s*2^N)^2 := by
  induction N with
  | zero => simpa using pow_nonneg hs 2
  | succ N ih =>
    rw [Finset.sum_range_succ,pow_succ (2:ℝ)]
    nlinarith [sq_nonneg (s*2^N)]

lemma sum_dyadic_cube_le {s : ℝ} (hs : 0 ≤ s) (N : ℕ) :
    ∑ j ∈ Finset.range N, (s*2^j)^3 ≤ (s*2^N)^3 := by
  induction N with
  | zero => simpa using pow_nonneg hs 3
  | succ N ih =>
    rw [Finset.sum_range_succ,pow_succ (2:ℝ)]
    have hp : 0 ≤ (s*2^N)^3 := by positivity
    nlinarith

lemma scalar_dyadic_inverse_sum (w : ℕ → ℝ) (N : ℕ) {s C : ℝ}
    (hs : 0 < s) (hC : 0 ≤ C) (hw : ∀ j, w j ≤ C/(s*2^j)) :
    ∑ j ∈ Finset.range N, w j ≤ 2*C/s := by
  calc
    _ ≤ ∑ j ∈ Finset.range N, (C/s)*(1/2:ℝ)^j :=
      Finset.sum_le_sum (fun j _ => (hw j).trans_eq (dyadic_reciprocal C s j))
    _ = (C/s)*∑ j ∈ Finset.range N, (1/2:ℝ)^j := (Finset.mul_sum _ _ _).symm
    _ ≤ (C/s)*2 := mul_le_mul_of_nonneg_left (sum_halves_le_two N) (div_nonneg hC hs.le)
    _ = _ := by ring

lemma scalar_dyadic_mixed_inverse_sum (w : ℕ → ℝ) (N : ℕ) {s a C : ℝ}
    (hs : 0 < s) (ha : 0 ≤ a) (hC : 0 ≤ C) (hw0 : ∀ j, 0 ≤ w j)
    (hnear : ∀ j, w j ≤ C/(s*2^j))
    (hoff : ∀ j, s*2^j ≤ a → w j ≤ C*(s*2^j)^2/a^3) :
    ∑ j ∈ Finset.range N, w j ≤ 12*C/(s+a) := by
  have hsa : 0 < s+a := add_pos_of_pos_of_nonneg hs ha
  by_cases has : a ≤ s
  · apply (scalar_dyadic_inverse_sum w N hs hC hnear).trans
    apply (div_le_div_iff₀ hs hsa).mpr
    nlinarith [mul_nonneg hC (sub_nonneg.mpr has),mul_nonneg hC hs.le]
  · have hsa' : s < a := lt_of_not_ge has
    have ha' : 0 < a := hs.trans hsa'
    obtain ⟨n,hn1,hn2⟩ := exists_nat_pow_near ((one_le_div hs).mpr hsa'.le) (by norm_num : (1:ℝ) < 2)
    let k := n+1
    have hbasele : s*2^k ≤ 2*a := by
      dsimp only [k]
      rw [pow_succ]
      have hn := (le_div_iff₀ hs).mp hn1
      nlinarith
    have hbaselt : a < s*2^k := by
      have hn := (div_lt_iff₀ hs).mp hn2
      simpa only [mul_comm] using hn
    have hinside : ∀ j < k, s*2^j ≤ a := by
      intro j hj
      have hpow := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show j ≤ n by omega)
      have hn := (le_div_iff₀ hs).mp hn1
      nlinarith [mul_le_mul_of_nonneg_left hpow hs.le]
    have hi : ∑ j ∈ Finset.range k, w j ≤ 4*C/a := by
      calc
        _ ≤ ∑ j ∈ Finset.range k, C*(s*2^j)^2/a^3 :=
          Finset.sum_le_sum (fun j hj => hoff j (hinside j (Finset.mem_range.mp hj)))
        _ = (C/a^3)*∑ j ∈ Finset.range k, (s*2^j)^2 := by rw [Finset.mul_sum]; congr 1; ext j; ring
        _ ≤ (C/a^3)*(s*2^k)^2 :=
          mul_le_mul_of_nonneg_left (sum_dyadic_square_le hs.le k) (by positivity)
        _ ≤ (C/a^3)*(2*a)^2 := by gcongr
        _ = _ := by field_simp; ring
    have ht : ∑ j ∈ Finset.range N, w (k+j) ≤ 2*C/a := by
      apply scalar_dyadic_inverse_sum _ N ha' hC
      intro j
      apply (hnear (k+j)).trans
      rw [pow_add,← mul_assoc]
      exact div_le_div_of_nonneg_left hC (mul_pos ha' (by positivity))
        (mul_le_mul_of_nonneg_right hbaselt.le (by positivity))
    have he : ∑ j ∈ Finset.range N, w j ≤ ∑ j ∈ Finset.range (k+N), w j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun j _ _ => hw0 j)
    rw [Finset.sum_range_add] at he
    apply (he.trans (add_le_add hi ht)).trans
    have hsum : 4*C/a+2*C/a = 6*C/a := by ring
    rw [hsum]
    apply (div_le_div_iff₀ ha' hsa).mpr
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hsa'.le)]

variable {V : Type*} [SeminormedAddCommGroup V]

lemma dyadic_mixed_inverse_bound (v₀ : V) (v : ℕ → V) (N : ℕ) {s a C : ℝ}
    (hs : 0 < s) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (h₀near : ‖v₀‖ ≤ C/s) (h₀off : s ≤ a → ‖v₀‖ ≤ C*s^2/a^3)
    (hnear : ∀ j < N, ‖v j‖ ≤ C/(s*2^j))
    (hoff : ∀ j < N, s*2^j ≤ a → ‖v j‖ ≤ C*(s*2^j)^2/a^3) :
    ‖v₀ + ∑ j ∈ Finset.range N, v j‖ ≤ 14*C/(s+a) := by
  have hsa : 0 < s+a := add_pos_of_pos_of_nonneg hs ha
  have hi : ‖v₀‖ ≤ 2*C/(s+a) := by
    by_cases has : a ≤ s
    · apply h₀near.trans
      apply (div_le_div_iff₀ hs hsa).mpr
      nlinarith [mul_nonneg hC (sub_nonneg.mpr has)]
    · have hsa' : s ≤ a := (lt_of_not_ge has).le
      have ha' : 0 < a := hs.trans_le hsa'
      have hb : C*s^2/a^3 ≤ C/a := by
        calc
          _ ≤ C*a^2/a^3 := by gcongr
          _ = _ := by field_simp
      apply ((h₀off hsa').trans hb).trans
      apply (div_le_div_iff₀ ha' hsa).mpr
      nlinarith [mul_nonneg hC (sub_nonneg.mpr hsa')]
  let w : ℕ → ℝ := fun j => if j < N then ‖v j‖ else 0
  have hw0 : ∀ j, 0 ≤ w j := by intro j; dsimp only [w]; split_ifs <;> positivity
  have hwn : ∀ j, w j ≤ C/(s*2^j) := by
    intro j
    dsimp only [w]
    split_ifs with hj
    · exact hnear j hj
    · positivity
  have hwo : ∀ j, s*2^j ≤ a → w j ≤ C*(s*2^j)^2/a^3 := by
    intro j hj
    dsimp only [w]
    split_ifs with hjN
    · exact hoff j hjN hj
    · positivity
  have hsum := scalar_dyadic_mixed_inverse_sum w N hs ha hC hw0 hwn hwo
  have he : ∑ j ∈ Finset.range N, w j = ∑ j ∈ Finset.range N, ‖v j‖ := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [w,ite_eq_left (Finset.mem_range.mp hj)]
  rw [he] at hsum
  calc
    _ ≤ ‖v₀‖ + ‖∑ j ∈ Finset.range N, v j‖ := norm_add_le _ _
    _ ≤ ‖v₀‖ + ∑ j ∈ Finset.range N, ‖v j‖ := add_le_add (le_refl _) (norm_sum_le _ _)
    _ ≤ 2*C/(s+a)+12*C/(s+a) := add_le_add hi hsum
    _ = _ := by ring

end TamingCompatibility.RadialPotential

end

end OAI
