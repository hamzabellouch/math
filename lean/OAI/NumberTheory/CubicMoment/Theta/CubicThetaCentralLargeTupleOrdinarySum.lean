import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleOrdinarySum
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralLargeTupleOrdinaryHigh

namespace OAI

/-! The actual high ordinary norm boxes, summed over the finite smooth
partition. The exceptional and cutoff boundary boxes remain separate. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


theorem largePrimeTupleOrdinaryHighSum_isLittleO_actual (i j : ℕ)
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C ξ δ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hδ : 0 < δ)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop, 0 < H X) :
    (fun X => largePrimeTupleOrdinaryHighSum i j ξ δ Ct (H X) X)
      =o[atTop] firstMomentScale := by
  obtain ⟨K,hK,hbound⟩ := largePrimeTuplePiece_ordinary_high_log_saving_actual i j hSW hpub
    hHuxley hperiod hMV hC hξ hξz hδ hGI hGQ  hGamma (3+(i+j)) Ct
  obtain ⟨D,hD,hcount⟩ := largePrimeTuplePartition_count i j
  apply Asymptotics.IsBigO.trans_isLittleO
    (g := fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^3) ?_ cubic_log_saving_isLittleO
  apply Asymptotics.IsBigO.of_bound (D*K)
  filter_upwards [hbound,hH,eventually_ge_atTop (1:ℝ)] with X hb hH hX
  let L := 1+Real.log X
  have hL : 0 < L := by dsimp [L]; linarith [Real.log_nonneg hX]
  let B := K*X^(5/6:ℝ)/L^(3+(i+j))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hp (d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
      ‖if X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) ∧
        (∃ q ∈ largePrimeTupleBox i j X,
          largePrimeTupleTerm i j 0 ξ Ct (H X) X q*normTupleWeight d (largePrimeTupleNorm q) ≠ 0 ∧
            ¬largePrimeTupleExceptional δ q) then
        largePrimeTuplePiece i j 0 ξ Ct (H X) X d else 0‖ ≤ B := by
    split_ifs with hd
    · exact hb (H X) hH d hd.1 hd.2
    · simpa only [norm_zero] using hB
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ X^(5/6:ℝ)/(1+Real.log X)^3)]
  unfold largePrimeTupleOrdinaryHighSum
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun d _ => hp d)).trans
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  apply (mul_le_mul_of_nonneg_right (hcount X hX) hB).trans_eq
  have hlogne : 1+Real.log X ≠ 0 := hL.ne'
  dsimp [B,L]
  rw [pow_add]
  field_simp [hlogne]
  ring

end CubicFirstMoment

end

end OAI
