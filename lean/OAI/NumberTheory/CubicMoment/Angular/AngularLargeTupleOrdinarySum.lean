import OAI.NumberTheory.CubicMoment.Angular.AngularLargeTupleOrdinaryHigh
import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleCount
import OAI.NumberTheory.CubicMoment.Estimates.PrimeModelLogTail

namespace OAI

/-! The actual high ordinary norm boxes, summed over the finite smooth
partition. The exceptional and cutoff boundary boxes remain separate. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

def angular_largePrimeTupleOrdinaryHighSum (i j : ℕ) (ξ δ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) ∧
      (∃ q ∈ largePrimeTupleBox i j X,
        largePrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight d (largePrimeTupleNorm q) ≠ 0 ∧
          ¬largePrimeTupleExceptional δ q) then
      largePrimeTuplePiece i j ℓ ξ Ct H X d else 0

theorem angular_largePrimeTupleOrdinaryHighSum_isLittleO (i j : ℕ)
    (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C ξ δ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hδ : 0 < δ)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput a)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop, 0 < H X) :
    (fun X => angular_largePrimeTupleOrdinaryHighSum ℓ i j ξ δ Ct (H X) X)
      =o[atTop] firstMomentScale := by
  obtain ⟨K,hK,hbound⟩ := angular_largePrimeTuplePiece_ordinary_high_log_saving ℓ i j hSW hℓ hpub
    hHuxley hperiod hMV hC hξ hξz hδ hGI hGQ hVor hGamma (3+(i+j)) Ct
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
          largePrimeTupleTerm i j ℓ ξ Ct (H X) X q*normTupleWeight d (largePrimeTupleNorm q) ≠ 0 ∧
            ¬largePrimeTupleExceptional δ q) then
        largePrimeTuplePiece i j ℓ ξ Ct (H X) X d else 0‖ ≤ B := by
    split_ifs with hd
    · exact hb (H X) hH d hd.1 hd.2
    · simpa only [norm_zero] using hB
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ X^(5/6:ℝ)/(1+Real.log X)^3)]
  unfold angular_largePrimeTupleOrdinaryHighSum
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
