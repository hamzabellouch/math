import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeGaussTailBound
import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeCentralWindow

namespace OAI

/-! Logarithmic cancellation for the literal semiprime Gauss tail in the
prime-detector decomposition, retaining every height window and norm piece. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

def semiprimeGaussTail (H T X : ℝ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    scaleFirstTailSemiprimeWindow 0 H (T*(3/2:ℝ)^s) X

theorem semiprimeGaussTail_log_saving
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) (k : ℕ) :
    ∃ (K : ℝ) (m : ℕ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ H T : ℝ, 1 ≤ H → H ≤ X^(1/6+1/3000:ℝ) →
      (1+Real.log X)^m ≤ T →
      ‖semiprimeGaussTail H T X‖ ≤ K*X^(5/6:ℝ)/(1+Real.log X)^k := by
  obtain ⟨K,m,hK,hbound⟩ := semiprimeGaussTail_piece_log_saving
    hpub hHuxley hperiod hMV hC hGI hGQ (k+3)
  obtain ⟨D,hD,hcount⟩ := semiprimePartitionCount_log_bound
  obtain ⟨E,hE,hheight⟩ := heightWindowCount_log_bound
  refine ⟨E*D^2*K,m,by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with X hbound hX
  intro H T hH hHX hT
  let N := normPartitionCount (3*X)
  let L := 1+Real.log X
  let B := K*X^(5/6:ℝ)/L^(k+3)
  have hL1 : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hX]
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hT1 : 1 ≤ T := (one_le_pow₀ hL1).trans hT
  have hTp : 0 < T := zero_lt_one.trans_le hT1
  have hHp : 0 < H := zero_lt_one.trans_le hH
  have hHle : H ≤ X := hHX.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX
      (by norm_num : (1/6+1/3000:ℝ) ≤ 1))
  have hM : (heightWindowCount H T:ℝ) ≤ E*L := by
    apply (hheight H T hH hT1).trans
    exact mul_le_mul_of_nonneg_left (by
      dsimp [L]
      linarith [Real.log_le_log hHp hHle]) hE.le
  have hn : (N:ℝ) ≤ D*L := hcount X hX
  have hwindow (s : ℕ) (hs : s ∈ Finset.range (heightWindowCount H T)) :
      ‖scaleFirstTailSemiprimeWindow 0 H (T*(3/2:ℝ)^s) X‖ ≤ (N:ℝ)^2*B := by
    obtain ⟨hlo,hhi⟩ := heightWindowCount_scale_bounds hHp hTp (Finset.mem_range.mp hs)
    have hpiece (i j : ℕ) : ‖semiprimeGaussTailPiece 0 H (T*(3/2:ℝ)^s) X i j‖ ≤ B :=
      hbound H _ i j hH hHX (hT.trans hlo) hhi
    have hrow (i : ℕ) :
        ‖∑ j ∈ Finset.range N, semiprimeGaussTailPiece 0 H (T*(3/2:ℝ)^s) X i j‖ ≤
          (N:ℝ)*B := by
      apply (norm_sum_le _ _).trans
      apply (Finset.sum_le_sum (fun j _ => hpiece i j)).trans_eq
      simp
    have hall : ‖∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        semiprimeGaussTailPiece 0 H (T*(3/2:ℝ)^s) X i j‖ ≤ (N:ℝ)^2*B := by
      apply (norm_sum_le _ _).trans
      apply (Finset.sum_le_sum (fun i _ => hrow i)).trans_eq
      simp [pow_two,mul_assoc]
    rw [scaleFirstTailSemiprimeWindow_partition 0 H _ hX,norm_mul]
    exact (mul_le_of_le_one_left (_root_.norm_nonneg _)
      (by norm_num : ‖(1/2:ℂ)‖ ≤ 1)).trans hall
  have hs : ‖semiprimeGaussTail H T X‖ ≤ (heightWindowCount H T:ℝ)*((N:ℝ)^2*B) := by
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

theorem semiprimeGaussTail_isLittleO
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ m : ℕ, ∀ Ct : ℕ, m ≤ Ct → ∀ H : ℝ → ℝ,
      (∀ᶠ X : ℝ in atTop, 1 ≤ H X ∧ H X ≤ X^(1/6+1/3000:ℝ)) →
      (fun X => semiprimeGaussTail (H X) ((1+Real.log X)^Ct) X)
        =o[atTop] firstMomentScale := by
  obtain ⟨K,m,hK,hbound⟩ := semiprimeGaussTail_log_saving
    hpub hHuxley hperiod hMV hC hGI hGQ 3
  refine ⟨m,?_⟩
  intro Ct hCt H hH
  apply Asymptotics.IsBigO.trans_isLittleO
    (g := fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^3) ?_ cubic_log_saving_isLittleO
  apply Asymptotics.IsBigO.of_bound K
  filter_upwards [hbound,hH,eventually_ge_atTop (1:ℝ)] with X hbound hH hX
  have hlogX : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ X^(5/6:ℝ)/(1+Real.log X)^3)]
  have ht : (1+Real.log X)^m ≤ (1+Real.log X)^Ct :=
    pow_le_pow_right₀ (by linarith [Real.log_nonneg hX]) hCt
  exact (hbound (H X) _ hH.1 hH.2 ht).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
