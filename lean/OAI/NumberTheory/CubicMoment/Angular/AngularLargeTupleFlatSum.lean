import OAI.NumberTheory.CubicMoment.Angular.AngularLargeTupleFlatHigh
import OAI.NumberTheory.CubicMoment.Estimates.FlatTripleNegligibleScale

namespace OAI

/-! Sum the actual high flat boxes, retaining their original sharp
distinguished-product condition. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

def angular_largePrimeTupleFlatHighSum (i j : ℕ) (ξ : ℝ) (Ct G : ℕ) (H X : ℝ) : ℂ :=
  ∑ d ∈ largePrimeTupleFlatBoxSet i j ℓ ξ Ct G H X,
    if X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
      largePrimeTuplePiece i j ℓ ξ Ct H X d else 0

theorem angular_largePrimeTupleFlatHighSum_isLittleO (i j : ℕ) (hij : i+j = 3)
    (hpnt : PrimaryPrimePNT) (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (Ct G : ℕ) (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop, 0 < H X) :
    (fun X => angular_largePrimeTupleFlatHighSum ℓ i j ξ Ct G (H X) X) =o[atTop] firstMomentScale := by
  obtain ⟨K,hK,hbound⟩ := angular_largePrimeTuplePiece_flat_high_bound ℓ i j hij hpnt hSW hℓ hpub
    hHuxley hperiod hMV hC hξ hξz hGI hGQ Ct G
  obtain ⟨D,hD,hcount⟩ := largePrimeTupleFlatBoxSet_count i j hij G
  apply Asymptotics.IsBigO.trans_isLittleO (g := fun X : ℝ =>
    X^(5/6:ℝ)*(1+Real.log (1+Real.log X))^4/(1+Real.log X)^(3/2:ℝ))
    ?_ flatTriple_counted_scale_isLittleO
  apply Asymptotics.IsBigO.of_bound (D*K)
  filter_upwards [hbound,hH,eventually_ge_atTop (1:ℝ)] with X hb hH hX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hQ : 0 < 1+Real.log (1+Real.log X) := by
    have hh := Real.log_nonneg (show 1 ≤ 1+Real.log X by linarith [Real.log_nonneg hX])
    linarith
  let B := K*X^(5/6:ℝ)*(1+Real.log (1+Real.log X))/(1+Real.log X)^(3/2:ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hp (d) (hd : d ∈ largePrimeTupleFlatBoxSet i j ℓ ξ Ct G (H X) X) :
      ‖if X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
        largePrimeTuplePiece i j ℓ ξ Ct (H X) X d else 0‖ ≤ B := by
    split_ifs with hh
    · exact hb (H X) hH d hd hh
    · simpa only [norm_zero] using hB
  rw [Real.norm_of_nonneg (by positivity)]
  unfold angular_largePrimeTupleFlatHighSum
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum hp).trans
  simp only [Finset.sum_const,nsmul_eq_mul]
  apply (mul_le_mul_of_nonneg_right (hcount ℓ ξ Ct (H X) X hX) hB).trans_eq
  dsimp [B]
  ring

end CubicFirstMoment

end

end OAI
