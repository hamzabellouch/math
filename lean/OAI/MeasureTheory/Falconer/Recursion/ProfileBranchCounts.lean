import OAI.MeasureTheory.Falconer.Recursion.ProfileNodeValues

namespace OAI

/-! Exact logarithmic coordinates for the retained block branching counts. -/
namespace Falconer.Regularization
variable {d : ℕ}

theorem blockSlope_mul_gap {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (F : CellPath d → List ℕ) (B i : ℕ) (p : CellPath d) :
    blockSlope L F N B i p*((blockDepth N B i : ℝ)-(blockDepth N B (i+1) : ℝ)) =
      (Nat.log 2 (labeledChildren L F (blockDepth N B (i+1)) (blockDepth N B i) p).card : ℝ)/(N : ℝ) := by
  unfold blockSlope
  by_cases he : (blockDepth N B i : ℝ)-(blockDepth N B (i+1) : ℝ) = 0
  · have hdep : blockDepth N B i = blockDepth N B (i+1) := by
      exact_mod_cast sub_eq_zero.mp he
    have hb := child_bin_le (blockDepth_antitone N B (Nat.le_succ i)) (Nat.sub_le _ _) hL F p
    have hd0 : d*(blockDepth N B i-blockDepth N B (i+1)) = 0 := by rw [hdep,Nat.sub_self,mul_zero]
    rw [hd0] at hb
    have hz := Nat.eq_zero_of_le_zero hb
    rw [hz,Nat.cast_zero,zero_div,zero_div,zero_mul]
  · exact div_mul_cancel₀ _ he

theorem regularizedProfile_node_difference {N : ℕ} (hN : 0 < N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (F : CellPath d → List ℕ)
    (B K : ℕ) (p : CellPath d) {i : ℕ} (hi : i ≤ K) :
    (N : ℝ)*(regularizedProfile L F N B K p N-
      regularizedProfile L F N B K p (blockDepth N B i)) =
      ∑ j ∈ Finset.range i,
        (Nat.log 2 (labeledChildren L F (blockDepth N B (j+1)) (blockDepth N B j) p).card : ℝ) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hp := finiteRampProfile_prefix (fun j => (blockDepth N B j : ℝ))
    (fun j => blockSlope L F N B j p)
    (show Antitone (fun j => (blockDepth N B j : ℝ)) from fun _ _ h =>
      Nat.cast_le.mpr (blockDepth_antitone N B h)) hi
  have hzero : (blockDepth N B 0 : ℝ) = N := by simp [blockDepth]
  rw [hzero] at hp
  change (N : ℝ)*(finiteRampProfile _ _ K N-finiteRampProfile _ _ K (blockDepth N B i)) = _
  rw [hp,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [blockSlope_mul_gap hL F B j p]
  exact mul_div_cancel₀ _ hn

theorem blockProduct_real_rpow (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B i : ℕ) (p : CellPath d) :
    (blockProduct L F N B i p : ℝ) =
      (2 : ℝ) ^ (∑ j ∈ Finset.range i,
        (Nat.log 2 (labeledChildren L F (blockDepth N B (j+1)) (blockDepth N B j) p).card : ℝ)) := by
  rw [blockProduct,Nat.cast_prod]
  simp only [blockBin,Nat.cast_pow,Nat.cast_ofNat]
  rw [← Nat.cast_sum,Real.rpow_natCast]
  exact Finset.prod_pow_eq_pow_sum _ _ _

theorem blockProduct_profile_difference {N : ℕ} (hN : 0 < N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (F : CellPath d → List ℕ)
    (B K : ℕ) (p : CellPath d) {i : ℕ} (hi : i ≤ K) :
    (blockProduct L F N B i p : ℝ) = (2 : ℝ)^((N : ℝ)*
      (regularizedProfile L F N B K p N-regularizedProfile L F N B K p (blockDepth N B i))) := by
  rw [regularizedProfile_node_difference hN hL F B K p hi]
  exact blockProduct_real_rpow L F N B i p

theorem blockProduct_ratio_profile {N : ℕ} (hN : 0 < N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (F : CellPath d → List ℕ)
    {B : ℕ} (hB : 0 < B) (p : CellPath d) {i : ℕ} (hi : i ≤ N/B+1) :
    (blockProduct L F N B (N/B+1) p : ℝ)/(blockProduct L F N B i p : ℝ) =
      (2 : ℝ)^((N : ℝ)*regularizedProfile L F N B (N/B+1) p (blockDepth N B i)) := by
  rw [blockProduct_profile_difference hN hL F B (N/B+1) p (le_refl _),
    blockProduct_profile_difference hN hL F B (N/B+1) p hi,
    blockDepth_terminal N hB,Nat.cast_zero,regularizedProfile_zero,sub_zero,← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

theorem blockProduct_inverse_ratio_profile {N : ℕ} (hN : 0 < N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (F : CellPath d → List ℕ)
    {B : ℕ} (hB : 0 < B) (p : CellPath d) {i : ℕ} (hi : i ≤ N/B+1) :
    (blockProduct L F N B i p : ℝ)/(blockProduct L F N B (N/B+1) p : ℝ) =
      (2 : ℝ)^(-((N : ℝ)*regularizedProfile L F N B (N/B+1) p (blockDepth N B i))) := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    ← blockProduct_ratio_profile hN hL F hB p hi,inv_div]

theorem regularizedProfile_lower_of_ratio_bound {N : ℕ} (hN : 0 < N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (F : CellPath d → List ℕ)
    {B : ℕ} (hB : 0 < B) (p : CellPath d) {i : ℕ} (hi : i ≤ N/B+1)
    {t A : ℝ}
    (hbound : (blockProduct L F N B i p : ℝ)/(blockProduct L F N B (N/B+1) p : ℝ) ≤
      (2 : ℝ)^(A-t*(blockDepth N B i : ℝ))) :
    t*(blockDepth N B i : ℝ)-A ≤
      (N : ℝ)*regularizedProfile L F N B (N/B+1) p (blockDepth N B i) := by
  rw [blockProduct_inverse_ratio_profile hN hL F hB p hi,
    Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)] at hbound
  linarith

end Falconer.Regularization

end OAI
