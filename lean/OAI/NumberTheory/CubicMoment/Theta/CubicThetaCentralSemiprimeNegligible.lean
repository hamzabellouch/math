import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeNegligible
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralSemiprimeLowKernel

namespace OAI

/-! The entire original radial semiprime branch is negligible, including
all norm pieces and all Mellin frequencies. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment


theorem centralSemiprimeProduct_isLittleO_actual
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop, 0 < H X) :
    (fun X => centralSemiprimeProduct 0 (H X) ((1+Real.log X)^Ct) X)
      =o[atTop] firstMomentScale := by
  obtain ⟨K,hK,hbound⟩ := semiprime_piece_log_saving_actual hSW hpub hHuxley hperiod
    hMV hC hGI hGQ  hGamma 5 Ct
  obtain ⟨D,hD,hcount⟩ := semiprimePartitionCount_log_bound
  apply Asymptotics.IsBigO.trans_isLittleO
    (g := fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^3) ?_ cubic_log_saving_isLittleO
  apply Asymptotics.IsBigO.of_bound (D^2*K)
  filter_upwards [hbound,hH,eventually_ge_atTop (1:ℝ)] with X hbound hH hX
  let N := normPartitionCount (3*X)
  let L := 1+Real.log X
  let B := K*X^(5/6:ℝ)/L^5
  have hL : 0 < L := by dsimp [L]; linarith [Real.log_nonneg hX]
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hrow (i : ℕ) :
      ‖∑ j ∈ Finset.range N, semiprimePartitionPiece 0 (H X) (L^Ct) X i j‖ ≤ (N:ℝ)*B := by
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum (fun j _ => hbound (H X) hH i j)).trans_eq
    simp [B,L]
  have hall : ‖∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      semiprimePartitionPiece 0 (H X) (L^Ct) X i j‖ ≤ (N:ℝ)^2*B := by
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum (fun i _ => hrow i)).trans_eq
    simp [pow_two,mul_assoc]
  have hs : ‖centralSemiprimeProduct 0 (H X) (L^Ct) X‖ ≤ (N:ℝ)^2*B := by
    rw [centralSemiprimeProduct_partition 0 (H X) (L^Ct) hX,norm_mul]
    exact (mul_le_of_le_one_left (_root_.norm_nonneg _) (by norm_num : ‖(1/2:ℂ)‖ ≤ 1)).trans hall
  have hn : (N:ℝ) ≤ D*L := hcount X hX
  have hn2 := pow_le_pow_left₀ (Nat.cast_nonneg N) hn 2
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ X^(5/6:ℝ)/(1+Real.log X)^3)]
  apply hs.trans
  calc
    _ ≤ (D*L)^2*B := mul_le_mul_of_nonneg_right hn2 hB
    _ = (D^2*K)*(X^(5/6:ℝ)/(1+Real.log X)^3) := by
      dsimp [B,L]
      field_simp [hL.ne']

end CubicFirstMoment

end

end OAI
