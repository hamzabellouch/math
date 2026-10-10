import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeGaussTailAngularHigh
import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeCentralWindow

namespace OAI

/-! Exact local-height separation of the angular semiprime tail. The high
part is negligible using all-height dispersion; the low part is left as the
literal finite sum to which the angular Hecke mean must be applied. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

def semiprimeGaussTailAngular (ℓ : ℤ) (H T X : ℝ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    scaleFirstTailSemiprimeWindow ℓ H (T*(3/2:ℝ)^s) X

def semiprimeGaussTailAngularLow (ℓ : ℤ) (H T X : ℝ) : ℂ :=
  (1/2:ℂ)*∑ s ∈ Finset.range (heightWindowCount H T),
    ∑ i ∈ Finset.range (normPartitionCount (3*X)),
      ∑ j ∈ Finset.range (normPartitionCount (3*X)),
        if T*(3/2:ℝ)^s ≤
            (min (semiprimePartitionScale i) (semiprimePartitionScale j))^(7/20:ℝ)
        then semiprimeGaussTailPiece ℓ H (T*(3/2:ℝ)^s) X i j else 0

def semiprimeGaussTailAngularHigh (ℓ : ℤ) (H T X : ℝ) : ℂ :=
  (1/2:ℂ)*∑ s ∈ Finset.range (heightWindowCount H T),
    ∑ i ∈ Finset.range (normPartitionCount (3*X)),
      ∑ j ∈ Finset.range (normPartitionCount (3*X)),
        if (min (semiprimePartitionScale i) (semiprimePartitionScale j))^(7/20:ℝ)
            < T*(3/2:ℝ)^s
        then semiprimeGaussTailPiece ℓ H (T*(3/2:ℝ)^s) X i j else 0

lemma semiprimeGaussTailAngular_split (ℓ : ℤ) (H T : ℝ) {X : ℝ} (hX : 1 ≤ X) :
    semiprimeGaussTailAngular ℓ H T X =
      semiprimeGaussTailAngularLow ℓ H T X + semiprimeGaussTailAngularHigh ℓ H T X := by
  unfold semiprimeGaussTailAngular semiprimeGaussTailAngularLow semiprimeGaussTailAngularHigh
  simp_rw [scaleFirstTailSemiprimeWindow_partition ℓ H _ hX]
  rw [← Finset.mul_sum,← mul_add]
  congr 1
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : T*(3/2:ℝ)^s ≤
      (min (semiprimePartitionScale i) (semiprimePartitionScale j))^(7/20:ℝ)
  · simp only [ite_eq_left h,not_lt_of_ge h,ite_false,add_zero]
  · simp only [ite_eq_right h,lt_of_not_ge h,ite_true,zero_add]

theorem semiprimeGaussTailAngularHigh_log_saving
    (hHuxley : HuxleyAdditiveLargeSieve) {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (ℓ : ℤ) (H T : ℝ), 1 ≤ H → H ≤ X^(1/6+1/3000:ℝ) → 1 ≤ T →
      ‖semiprimeGaussTailAngularHigh ℓ H T X‖ ≤
        K*X^(5/6:ℝ)/(1+Real.log X)^k := by
  obtain ⟨K,hK,hbound⟩ := semiprimeGaussTail_angular_high_piece hHuxley hMV hC (k+3)
  obtain ⟨D,hD,hcount⟩ := semiprimePartitionCount_log_bound
  obtain ⟨E,hE,hheight⟩ := heightWindowCount_log_bound
  refine ⟨E*D^2*K,by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with X hbound hX
  intro ℓ H T hH hHX hT
  let N := normPartitionCount (3*X)
  let L := 1+Real.log X
  let B := K*X^(5/6:ℝ)/L^(k+3)
  have hL1 : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hX]
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hHp : 0 < H := zero_lt_one.trans_le hH
  have hHle : H ≤ X := hHX.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX
      (by norm_num : (1/6+1/3000:ℝ) ≤ 1))
  have hM : (heightWindowCount H T:ℝ) ≤ E*L := by
    apply (hheight H T hH hT).trans
    exact mul_le_mul_of_nonneg_left (by
      dsimp [L]
      linarith [Real.log_le_log hHp hHle]) hE.le
  have hn : (N:ℝ) ≤ D*L := hcount X hX
  let f := fun (s i j : ℕ) =>
    if (min (semiprimePartitionScale i) (semiprimePartitionScale j))^(7/20:ℝ)
        < T*(3/2:ℝ)^s
    then semiprimeGaussTailPiece ℓ H (T*(3/2:ℝ)^s) X i j else 0
  have hwindow (s : ℕ) (hs : s ∈ Finset.range (heightWindowCount H T)) :
      ‖∑ i ∈ Finset.range N,∑ j ∈ Finset.range N,f s i j‖ ≤ (N:ℝ)^2*B := by
    obtain ⟨_,hhi⟩ := heightWindowCount_scale_bounds hHp hTp (Finset.mem_range.mp hs)
    have hpiece (i j : ℕ) : ‖f s i j‖ ≤ B := by
      dsimp [f]
      split_ifs with hh
      · exact hbound ℓ H _ i j hH hHX hhi hh
      · simpa only [norm_zero] using hB
    have hrow (i : ℕ) : ‖∑ j ∈ Finset.range N,f s i j‖ ≤ (N:ℝ)*B := by
      apply (norm_sum_le _ _).trans
      apply (Finset.sum_le_sum (fun j _ => hpiece i j)).trans_eq
      simp
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum (fun i _ => hrow i)).trans_eq
    simp [pow_two,mul_assoc]
  have hs : ‖semiprimeGaussTailAngularHigh ℓ H T X‖ ≤
      (heightWindowCount H T:ℝ)*((N:ℝ)^2*B) := by
    change ‖(1/2:ℂ)*∑ s ∈ Finset.range (heightWindowCount H T),
      ∑ i ∈ Finset.range N,∑ j ∈ Finset.range N,f s i j‖ ≤ _
    rw [norm_mul]
    apply (mul_le_of_le_one_left (_root_.norm_nonneg _)
      (by norm_num : ‖(1/2:ℂ)‖ ≤ 1)).trans
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum hwindow).trans_eq
    simp
  apply hs.trans
  calc
    _ ≤ (E*L)*((D*L)^2*B) := mul_le_mul hM
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg N) hn 2) hB)
      (by positivity) (by positivity)
    _ = (E*D^2*K)*X^(5/6:ℝ)/(1+Real.log X)^k := by
      change (E*L)*((D*L)^2*(K*X^(5/6:ℝ)/L^(k+3))) =
        (E*D^2*K)*X^(5/6:ℝ)/L^k
      rw [pow_add]
      field_simp [hL.ne']

theorem semiprimeGaussTailAngularHigh_isLittleO
    (hHuxley : HuxleyAdditiveLargeSieve) {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (ℓ : ℝ → ℤ) (H T : ℝ → ℝ)
    (hH : ∀ᶠ X : ℝ in atTop, 1 ≤ H X ∧ H X ≤ X^(1/6+1/3000:ℝ))
    (hT : ∀ᶠ X : ℝ in atTop, 1 ≤ T X) :
    (fun X => semiprimeGaussTailAngularHigh (ℓ X) (H X) (T X) X)
      =o[atTop] firstMomentScale := by
  obtain ⟨K,hK,hbound⟩ := semiprimeGaussTailAngularHigh_log_saving hHuxley hMV hC 3
  apply Asymptotics.IsBigO.trans_isLittleO
    (g := fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^3) ?_ cubic_log_saving_isLittleO
  apply Asymptotics.IsBigO.of_bound K
  filter_upwards [hbound,hH,hT,eventually_ge_atTop (1:ℝ)] with X hbound hH hT hX
  have hlog : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ X^(5/6:ℝ)/(1+Real.log X)^3)]
  exact (hbound (ℓ X) (H X) (T X) hH.1 hH.2 hT).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
