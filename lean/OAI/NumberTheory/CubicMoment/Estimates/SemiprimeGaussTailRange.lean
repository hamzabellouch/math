import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeGaussTailPartition
import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeRange
import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeMiddleRange

namespace OAI

/-! The original nonzero Gauss window supplies its actual prime lengths.
No range is inferred from the centered semiprime kernel. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma semiprimeGaussTail_kernel_product_range (ℓ : ℤ) (H T : ℝ)
    {X : ℝ} (hX : 0 < X) {p q : Eisenstein}
    (hk : scaleFirstTailKernel ℓ H T X (p*q) ≠ 0) :
    X/2 ≤ norm (p*q) ∧ norm (p*q) ≤ 3*X := by
  have hw : primeProductEnvelope (norm (p*q)/X) ≠ 0 := by
    intro hz
    apply hk
    simp only [scaleFirstTailKernel,hz,mul_zero,zero_mul]
  constructor
  · apply le_of_not_gt
    intro hh
    apply hw
    exact primeProductEnvelope_zero_lower ((div_le_iff₀ hX).mpr (by linarith))
  · apply le_of_not_gt
    intro hh
    apply hw
    exact primeProductEnvelope_zero ((le_div_iff₀ hX).mpr hh.le)

lemma semiprimeGaussTail_piece_lengths (ℓ : ℤ) (H T : ℝ)
    {X : ℝ} (hX : 0 < X) {i j : ℕ} {p q : Eisenstein}
    (hp : semiprimePartitionCoefficient X i p ≠ 0)
    (hq : semiprimePartitionCoefficient X j q ≠ 0)
    (hk : scaleFirstTailKernel ℓ H T X (p*q) ≠ 0) :
    X/8 ≤ semiprimePartitionScale i*semiprimePartitionScale j ∧
      semiprimePartitionScale i*semiprimePartitionScale j ≤ 3*X ∧
      X^(2/5:ℝ)/2 ≤ semiprimePartitionScale i ∧
      X^(2/5:ℝ)/2 ≤ semiprimePartitionScale j := by
  obtain ⟨hpr,hpl,hpu⟩ := semiprimePartitionCoefficient_range hX hp
  obtain ⟨hqr,hql,hqu⟩ := semiprimePartitionCoefficient_range hX hq
  obtain ⟨hl,hu⟩ := semiprimeGaussTail_kernel_product_range ℓ H T hX hk
  rw [norm_mul_eq] at hl hu
  have ha := (semiprimePartitionScale_pos i).le
  have hb := (semiprimePartitionScale_pos j).le
  have hlow := mul_le_mul hpl hql hb (norm_nonneg p)
  have hhigh := mul_le_mul hpu hqu (norm_nonneg q) (by positivity : 0 ≤ 2*semiprimePartitionScale i)
  exact ⟨by nlinarith,hlow.trans hu,by linarith,by linarith⟩

lemma semiprimeGaussTailPiece_symm (ℓ : ℤ) (H T X : ℝ) (i j : ℕ) :
    semiprimeGaussTailPiece ℓ H T X i j = semiprimeGaussTailPiece ℓ H T X j i := by
  unfold semiprimeGaussTailPiece
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [mul_comm q p]
  ring

lemma semiprimeGaussTailPiece_nonzero_lengths (ℓ : ℤ) (H T : ℝ)
    {X : ℝ} (hX : 0 < X) {i j : ℕ}
    (hne : semiprimeGaussTailPiece ℓ H T X i j ≠ 0) :
    X/8 ≤ semiprimePartitionScale i*semiprimePartitionScale j ∧
      semiprimePartitionScale i*semiprimePartitionScale j ≤ 3*X ∧
      X^(2/5:ℝ)/2 ≤ semiprimePartitionScale i ∧
      X^(2/5:ℝ)/2 ≤ semiprimePartitionScale j := by
  have hex : ∃ p ∈ primeCutoff (3*X), ∃ q ∈ primeCutoff (3*X),
      semiprimePartitionCoefficient X i p*semiprimePartitionCoefficient X j q*
        scaleFirstTailKernel ℓ H T X (p*q) ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hne (Finset.sum_eq_zero (fun p hp => Finset.sum_eq_zero (fun q hq => hn p hp q hq)))
  obtain ⟨p,_,q,_,hpq⟩ := hex
  exact semiprimeGaussTail_piece_lengths ℓ H T hX
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hpq).1).1
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hpq).1).2 (mul_ne_zero_iff.mp hpq).2

theorem eventually_semiprimeGaussTail_admissible {η : ℝ} (hη : 0 < η) (G : ℕ) (B₀ : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ (ℓ : ℤ) (H T : ℝ) (i j : ℕ),
      semiprimePartitionScale j ≤ semiprimePartitionScale i →
      semiprimeGaussTailPiece ℓ H T X i j ≠ 0 →
      B₀ ≤ semiprimePartitionScale j ∧
      (2*semiprimePartitionScale j)^(1/2:ℝ) < semiprimePartitionScale j ∧
      (semiprimePartitionScale j)^(1-η/16) ≤ semiprimePartitionScale i ∧
      semiprimePartitionScale i ≤
        (semiprimePartitionScale j)^2/(1+Real.log (semiprimePartitionScale j))^G := by
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_semiprime_upper_range G,
    eventually_const_mul_rpow_le (by norm_num : (39/100:ℝ) < 2/5) 2,
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 39/100)).eventually_ge_atTop (max B₀ 4)]
    with X hX hupper hlower hlarge
  intro ℓ H T i j hji hne
  have hXp : 0 < X := zero_lt_one.trans_le hX
  obtain ⟨_,hprod,_,hrough⟩ := semiprimeGaussTailPiece_nonzero_lengths ℓ H T hXp hne
  have hB : X^(39/100:ℝ) ≤ semiprimePartitionScale j := by linarith
  have hB4 : 4 ≤ semiprimePartitionScale j :=
    (le_max_right B₀ 4).trans (hlarge.trans hB)
  have hBp := semiprimePartitionScale_pos j
  refine ⟨(le_max_left B₀ 4).trans (hlarge.trans hB),?_,?_,hupper _ _ hB hprod⟩
  · have hh := Real.rpow_lt_rpow (by positivity : (0:ℝ) ≤ 2*semiprimePartitionScale j)
      (by nlinarith : 2*semiprimePartitionScale j < (semiprimePartitionScale j)^2)
      (by norm_num : (0:ℝ) < 1/2)
    have he : ((semiprimePartitionScale j)^2)^(1/2:ℝ) = semiprimePartitionScale j := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hBp.le]
      norm_num
    rwa [he] at hh
  · apply (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ semiprimePartitionScale j)
      (by linarith : 1-η/16 ≤ (1:ℝ))).trans
    simpa only [Real.rpow_one] using hji


end CubicFirstMoment

end

end OAI
