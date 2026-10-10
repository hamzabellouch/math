import Mathlib
import OAI.Analysis.WeakInfiniteness.FreeTwistedNorm

namespace OAI

noncomputable section

noncomputable section

open scoped ENNReal InnerProductSpace

namespace WeakPureInfiniteness

variable {G K : Type*}

variable [Group G]

section SchurBound

variable {X I : Type*} [Fintype I]

lemma l2_summable_norm_sq (ξ : GroupHilbert X) : Summable (fun x => ‖ξ x‖ ^ 2) := by
  have h := Memℓp.summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) ξ.property
  norm_num at h
  exact h

lemma l2_norm_sq (ξ : GroupHilbert X) : ‖ξ‖ ^ 2 = ∑' x, ‖ξ x‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) ξ
  norm_num at h
  exact h

lemma weighted_two_mul_le (a b w : ℝ) (hw : 0 < w) :
    2 * a * b ≤ w * a ^ 2 + w⁻¹ * b ^ 2 := by
  have h := sq_nonneg (w * a - b)
  have hi : w * w⁻¹ = 1 := mul_inv_cancel₀ hw.ne'
  apply (mul_le_mul_iff_right₀ hw).mp
  nlinarith

def permutationSum (e : I → X ≃ X) : GroupHilbert X →L[ℂ] GroupHilbert X :=
  ∑ i, (l2Reindex (e i)).toContinuousLinearEquiv.toContinuousLinearMap

lemma weighted_squares_summable (w : X → ℝ) (hw : ∀ x, 0 < w x)
    (e : I → X ≃ X) (C : ℝ)
    (hrow : ∀ x, ∑ i, w ((e i).symm x) / w x ≤ C)
    (ξ : GroupHilbert X) (i : I) :
    Summable (fun x => (w ((e i).symm x) / w x) * ‖ξ x‖ ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun x => mul_nonneg (div_nonneg (hw _).le (hw _).le) (sq_nonneg _))
    (fun x => mul_le_mul_of_nonneg_right
      ((Finset.single_le_sum (fun j _ => div_nonneg (hw _).le (hw _).le)
        (Finset.mem_univ i)).trans (hrow x)) (sq_nonneg _))
    ((l2_summable_norm_sq ξ).mul_left C)

lemma weighted_squares_sum_le (w : X → ℝ) (hw : ∀ x, 0 < w x)
    (e : I → X ≃ X) (C : ℝ)
    (hrow : ∀ x, ∑ i, w ((e i).symm x) / w x ≤ C)
    (ξ : GroupHilbert X) :
    ∑ i, ∑' x, (w ((e i).symm x) / w x) * ‖ξ x‖ ^ 2 ≤ C * ‖ξ‖ ^ 2 := by
  have hs (i : I) := weighted_squares_summable w hw e C hrow ξ i
  rw [← Summable.tsum_finsetSum (fun i _ => hs i)]
  simp_rw [← Finset.sum_mul]
  rw [l2_norm_sq ξ, ← tsum_mul_left]
  apply Summable.tsum_le_tsum
    (fun x => mul_le_mul_of_nonneg_right (hrow x) (sq_nonneg _))
  · simpa only [Finset.sum_mul] using summable_sum (fun i _ => hs i)
  · exact (l2_summable_norm_sq ξ).mul_left C

theorem norm_permutationSum_le (w : X → ℝ) (hw : ∀ x, 0 < w x)
    (e : I → X ≃ X) (C : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ x, ∑ i, w ((e i).symm x) / w x ≤ C)
    (hcol : ∀ x, ∑ i, w (e i x) / w x ≤ C) :
    ‖permutationSum e‖ ≤ C := by
  classical
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le hC
  intro ξ η hξ hη
  have hs₁ (i : I) := weighted_squares_summable w hw e C hrow η i
  have hs₂ (i : I) : Summable (fun x =>
      (w x / w ((e i).symm x)) * ‖ξ ((e i).symm x)‖ ^ 2) := by
    have h := weighted_squares_summable w hw (fun i => (e i).symm) C hcol ξ i
    convert (e i).symm.summable_iff.mpr h using 1
    ext x
    simp
  have hpoint (i : I) (x : X) :
      2 * (inner ℂ (ξ ((e i).symm x)) (η x)).re ≤
        (w ((e i).symm x) / w x) * ‖η x‖ ^ 2 +
        (w x / w ((e i).symm x)) * ‖ξ ((e i).symm x)‖ ^ 2 := by
    have hr := (Complex.re_le_norm (inner ℂ (ξ ((e i).symm x)) (η x))).trans
      (norm_inner_le_norm (ξ ((e i).symm x)) (η x))
    have he := weighted_two_mul_le ‖η x‖ ‖ξ ((e i).symm x)‖
      (w ((e i).symm x) / w x) (div_pos (hw _) (hw _))
    rw [inv_div] at he
    nlinarith
  have hi (i : I) :
      2 * (inner ℂ (l2Reindex (e i) ξ) η).re ≤
        (∑' x, (w ((e i).symm x) / w x) * ‖η x‖ ^ 2) +
        (∑' x, (w x / w ((e i).symm x)) * ‖ξ ((e i).symm x)‖ ^ 2) := by
    have hin := lp.summable_inner (𝕜 := ℂ) (l2Reindex (e i) ξ) η
    have hre := (Complex.reCLM.hasSum hin.hasSum).summable
    have hret : (inner ℂ (l2Reindex (e i) ξ) η).re =
        ∑' x, (inner ℂ (ξ ((e i).symm x)) (η x)).re := by
      exact Complex.reCLM.map_tsum hin
    rw [hret, ← tsum_mul_left, ← (hs₁ i).tsum_add (hs₂ i)]
    exact Summable.tsum_le_tsum (hpoint i) (hre.mul_left 2) ((hs₁ i).add (hs₂ i))
  have hsecond :
      (∑ i, ∑' x, (w x / w ((e i).symm x)) * ‖ξ ((e i).symm x)‖ ^ 2) =
      (∑ i, ∑' x, (w (e i x) / w x) * ‖ξ x‖ ^ 2) := by
    apply Finset.sum_congr rfl
    intro i _
    convert (e i).symm.tsum_eq (fun x => (w (e i x) / w x) * ‖ξ x‖ ^ 2) using 1
    simp
  have htotal := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  rw [Finset.sum_add_distrib, hsecond] at htotal
  have hb₁ := weighted_squares_sum_le w hw e C hrow η
  have hb₂ := weighted_squares_sum_le w hw (fun i => (e i).symm) C hcol ξ
  simp only [Equiv.symm_symm] at hb₂
  have heval : (inner ℂ (permutationSum e ξ) η).re =
      ∑ i, (inner ℂ (l2Reindex (e i) ξ) η).re := by
    simp [permutationSum]
  change (inner ℂ (permutationSum e ξ) η).re ≤ C
  rw [heval]
  rw [← Finset.mul_sum] at htotal
  simp only [hξ, hη, one_pow, mul_one] at hb₁ hb₂
  nlinarith

end SchurBound

def inverseLetterEquiv : FreeLetter ≃ FreeLetter where
  toFun := inverseLetter
  invFun := inverseLetter
  left_inv := inverseLetter_inverseLetter
  right_inv := inverseLetter_inverseLetter

lemma freeTreeWeight_inverse_sum_le (g : FreeTwo) :
    ∑ s : FreeLetter, freeTreeWeight ((freeLetter s)⁻¹ * g) / freeTreeWeight g ≤
      2 * Real.sqrt 3 := by
  have he := inverseLetterEquiv.sum_comp
    (fun s => freeTreeWeight (freeLetter s * g) / freeTreeWeight g)
  simp only [inverseLetterEquiv, Equiv.coe_fn_mk, freeLetter_inverseLetter] at he
  rw [he]
  exact freeTreeWeight_sum_le g

def freeTreeAdjacency : GroupHilbert FreeTwo →L[ℂ] GroupHilbert FreeTwo :=
  ∑ s : FreeLetter, (leftRegular (freeLetter s) : GroupHilbert FreeTwo →L[ℂ] GroupHilbert FreeTwo)

theorem norm_freeTreeAdjacency_le : ‖freeTreeAdjacency‖ ≤ 2 * Real.sqrt 3 := by
  have h := norm_permutationSum_le freeTreeWeight freeTreeWeight_pos
    (fun s : FreeLetter => Equiv.mulLeft (freeLetter s)) (2 * Real.sqrt 3)
    (by positivity)
    (by simpa using freeTreeWeight_inverse_sum_le)
    (by simpa using freeTreeWeight_sum_le)
  exact h

theorem norm_freeTreeAdjacency_lt_four : ‖freeTreeAdjacency‖ < 4 :=
  norm_freeTreeAdjacency_le.trans_lt freeTree_norm_gap

end WeakPureInfiniteness
end
end

end OAI
