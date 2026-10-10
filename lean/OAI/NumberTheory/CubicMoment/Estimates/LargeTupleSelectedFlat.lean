import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleFlatSum

namespace OAI

/-! Any selected subfamily of actual high flat boxes has the same
negligible bound. This will select the exceptional contribution exactly. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largePrimeTupleSelectedFlatHighSum (i j : ℕ) (ξ : ℝ) (Ct G : ℕ) (H X : ℝ)
    (select : ((Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) → Prop) : ℂ :=
  ∑ d ∈ largePrimeTupleFlatBoxSet i j 0 ξ Ct G H X,
    if X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) ∧ select d then
      largePrimeTuplePiece i j 0 ξ Ct H X d else 0

theorem largePrimeTupleSelectedFlatHighSum_isLittleO (i j : ℕ) (hij : i+j = 3)
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (Ct G : ℕ)
    (select : (X : ℝ) → (((Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) → Prop))
    (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop, 0 < H X) :
    (fun X => largePrimeTupleSelectedFlatHighSum i j ξ Ct G (H X) X (select X)) =o[atTop] firstMomentScale := by
  obtain ⟨K,hK,hbound⟩ := largePrimeTuplePiece_flat_high_bound i j hij hpnt hSW hpub
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
  have hp (d) (hd : d ∈ largePrimeTupleFlatBoxSet i j 0 ξ Ct G (H X) X) :
      ‖if X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) ∧ select X d then
        largePrimeTuplePiece i j 0 ξ Ct (H X) X d else 0‖ ≤ B := by
    split_ifs with hh
    · exact hb (H X) hH d hd hh.1
    · simpa only [norm_zero] using hB
  rw [Real.norm_of_nonneg (by positivity)]
  unfold largePrimeTupleSelectedFlatHighSum
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum hp).trans
  simp only [Finset.sum_const,nsmul_eq_mul]
  apply (mul_le_mul_of_nonneg_right (hcount 0 ξ Ct (H X) X hX) hB).trans_eq
  dsimp [B]
  ring

end CubicFirstMoment

end

end OAI
