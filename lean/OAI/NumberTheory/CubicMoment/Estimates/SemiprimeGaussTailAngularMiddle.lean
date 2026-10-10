import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeGaussTailAngularAlgebra
import OAI.NumberTheory.CubicMoment.Estimates.PrimeGroupTailEnvelope

namespace OAI

/-! The all-height middle-range semiprime tail remains valid with every
fixed angular twist. Its constants are independent of the angular index. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def semiprimeAngularEnvelopeTail (ℓ : ℤ) (H U X : ℝ) (i j : ℕ) : ℂ :=
  envelopeCutoffBilinearTail (semiprimeFullSupport X i) (semiprimeFullSupport X j)
    (semiprimeAngularCoefficient ℓ X i) (semiprimeAngularCoefficient ℓ X j)
    primeProductEnvelope H U X

theorem semiprimeGaussTail_angular_middle_tail
    (hHuxley : HuxleyAdditiveLargeSieve) {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (k : ℕ) :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ (ℓ : ℤ) (H U X : ℝ) (i j : ℕ),
      B₀ ≤ semiprimePartitionScale j →
      (4*semiprimePartitionScale j)^(27/25:ℝ) ≤ semiprimePartitionScale i →
      semiprimePartitionScale i ≤ (semiprimePartitionScale j)^(19/10:ℝ) →
      (4*semiprimePartitionScale j)^(1/50:ℝ) ≤ U →
      1 ≤ H → H ≤ (semiprimePartitionScale j)^3 → 0 < X →
      ‖semiprimeAngularEnvelopeTail ℓ H U X i j‖ ≤
        K*(semiprimePartitionScale i)^(5/6:ℝ)*(semiprimePartitionScale j)^(5/6:ℝ)/
          (1+Real.log (semiprimePartitionScale j))^k := by
  obtain ⟨K,B₀,hK,hbound⟩ := primeGroupTail_envelope_log_saving
    (Mα:=36) (Mβ:=36) (D:=2) hMV hC hHuxley (by norm_num) (by norm_num)
    (by norm_num) k 0 0 2 primeProductEnvelope primeProductEnvelope_compact
    primeProductEnvelope_positive primeProductEnvelope_smooth
  refine ⟨K,B₀,hK,?_⟩
  intro ℓ H U X i j hB hA hAU hU hH hHB hX
  apply hbound _ _ _ _ (semiprimePartitionScale j) (semiprimePartitionScale i)
    U H X hB (by simpa only [show (2:ℝ)*2=4 by norm_num] using hA) hAU
    (by simpa only [show (2:ℝ)*2=4 by norm_num] using hU) hH hHB hX
  · intro p hp
    exact semiprimeFullSupport_bounds hX i hp
  · intro p hp
    have hs := semiprimeFullSupport_bounds hX j hp
    have hprime := (semiprimeFullSupport_mem X j p).mp hp
    exact ⟨hs.1,hprime.1.2.squarefree,hs.2⟩
  · simpa only [pow_zero,mul_one] using semiprimeAngularCoefficient_energy ℓ hX i
  · simpa only [pow_zero,mul_one] using semiprimeAngularCoefficient_energy ℓ hX j

theorem semiprimeGaussTail_angular_middle_window
    (hHuxley : HuxleyAdditiveLargeSieve) {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (k : ℕ) :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ (ℓ : ℤ) (H U X : ℝ) (i j : ℕ),
      B₀ ≤ semiprimePartitionScale j →
      (4*semiprimePartitionScale j)^(27/25:ℝ) ≤ semiprimePartitionScale i →
      semiprimePartitionScale i ≤ (semiprimePartitionScale j)^(19/10:ℝ) →
      (4*semiprimePartitionScale j)^(1/50:ℝ) ≤ U →
      1 ≤ H → H ≤ (semiprimePartitionScale j)^3 → 0 < X → U < 2*Real.pi*H →
      ‖semiprimeGaussTailPiece ℓ H U X i j‖ ≤
        K*(semiprimePartitionScale i)^(5/6:ℝ)*(semiprimePartitionScale j)^(5/6:ℝ)/
          (1+Real.log (semiprimePartitionScale j))^k := by
  obtain ⟨K,B₀,hK,hbound⟩ := semiprimeGaussTail_angular_middle_tail hHuxley hMV hC k
  refine ⟨2*K,B₀,by positivity,?_⟩
  intro ℓ H U X i j hB hA hAU hU hH hHB hX hcap
  have hUp : 0 < U := (Real.rpow_pos_of_pos
    (mul_pos (by norm_num : (0:ℝ) < 4) (semiprimePartitionScale_pos j)) _).trans_le hU
  have hU' : (4*semiprimePartitionScale j)^(1/50:ℝ) ≤ U*(3/2) := hU.trans (by linarith)
  have hfirst := hbound ℓ H U X i j hB hA hAU hU hH hHB hX
  have hlast := hbound ℓ H (U*(3/2)) X i j hB hA hAU hU' hH hHB hX
  rw [semiprimeGaussTailPiece_angular_window ℓ H U hX i j,
    productGaussWindow_eq_tail_sub _ _ _ _ _ (zero_lt_one.trans_le hH) hUp hcap X]
  exact (norm_sub_le _ _).trans ((add_le_add hfirst hlast).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
