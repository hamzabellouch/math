import OAI.NumberTheory.CubicMoment.Angular.AngularLargeTupleExceptionalHigh
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralAngularLargeTupleNonflatHigh

namespace OAI

/-! The remaining high exceptional boxes split exactly into the flat
subfamily and its complement. Both are negligible on the stated scale. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)


theorem angular_largePrimeTupleExceptionalHighSum_isLittleO_actual (i j : ℕ) (hij : i+j = 3)
    (hpnt : PrimaryPrimePNT) (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ δ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hδ : δ ≤ 1/12)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop, 0 < H X) :
    (fun X => angular_largePrimeTupleExceptionalHighSum ℓ i j ξ δ Ct (H X) X) =o[atTop] firstMomentScale := by
  obtain ⟨G,K,hK,hbound⟩ := angular_largePrimeTuplePiece_nonflat_high_bound_actual ℓ i j hij hSW hℓ hpub
    hHuxley hperiod hMV hC hξ hξz hδ hGI hGQ  hGamma (3+(i+j)) Ct
  obtain ⟨D,hD,hcount⟩ := largePrimeTuplePartition_count i j
  have hn : (fun X => angular_largePrimeTupleExceptionalNonflatSum ℓ i j ξ δ Ct G (H X) X)
      =o[atTop] firstMomentScale := by
    apply Asymptotics.IsBigO.trans_isLittleO
      (g := fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^3) ?_ cubic_log_saving_isLittleO
    apply Asymptotics.IsBigO.of_bound (D*K)
    filter_upwards [hbound,hH,eventually_ge_atTop (1:ℝ)] with X hb hH hX
    have hXp : 0 < X := zero_lt_one.trans_le hX
    have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
    let B := K*X^(5/6:ℝ)/(1+Real.log X)^(3+(i+j))
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hp (d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
        ‖if (X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) ∧
          angular_largeTupleExceptionalSelector ℓ i j ξ δ Ct (H X) X d) ∧
          d ∉ largePrimeTupleFlatBoxSet i j ℓ ξ Ct G (H X) X then
          largePrimeTuplePiece i j ℓ ξ Ct (H X) X d else 0‖ ≤ B := by
      split_ifs with hd
      · by_cases hz : largePrimeTuplePiece i j ℓ ξ Ct (H X) X d = 0
        · rw [hz,norm_zero]; exact hB
        obtain ⟨q,hq,hqne⟩ := largePrimeTuplePiece_witness d hz
        have hex : largePrimeTupleExceptional δ q := by
          by_contra hh
          exact hd.1.2 ⟨q,hq,hqne,hh⟩
        exact hb (H X) hH d hd.1.1 hd.2 ⟨q,hq,hqne,hex⟩
      · simpa only [norm_zero] using hB
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ X^(5/6:ℝ)/(1+Real.log X)^3)]
    unfold angular_largePrimeTupleExceptionalNonflatSum
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum (fun d _ => hp d)).trans
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    apply (mul_le_mul_of_nonneg_right (hcount X hX) hB).trans_eq
    dsimp [B]
    rw [pow_add]
    field_simp
    ring
  have hf := angular_largePrimeTupleSelectedFlatHighSum_isLittleO ℓ i j hij hpnt hSW hℓ hpub hHuxley
    hperiod hMV hC hξ hξz hGI hGQ Ct G
    (fun X => angular_largeTupleExceptionalSelector ℓ i j ξ δ Ct (H X) X) H hH
  have he : (fun X => angular_largePrimeTupleExceptionalHighSum ℓ i j ξ δ Ct (H X) X) =
      (fun X => angular_largePrimeTupleSelectedFlatHighSum ℓ i j ξ Ct G (H X) X
        (angular_largeTupleExceptionalSelector ℓ i j ξ δ Ct (H X) X) +
        angular_largePrimeTupleExceptionalNonflatSum ℓ i j ξ δ Ct G (H X) X) := by
    funext X
    exact angular_largePrimeTupleExceptionalHigh_split ℓ i j ξ δ Ct G (H X) X
  rw [he]
  exact hf.add hn

end CubicFirstMoment

end

end OAI
