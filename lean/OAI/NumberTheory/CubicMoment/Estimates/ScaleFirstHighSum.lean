import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstMiddleSum
import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleHighSum

namespace OAI

/-! The complete manuscript high-scale branch is negligible. The new
middle interval is treated by its distinguished group; the higher
interval is exactly the already proved large-row high sum. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma scaleFirstPrimeTuplePiece_eq_high (i j : ℕ) (ℓ : ℤ) (ξ : ℝ)
    (Ct : ℕ) (H : ℝ) {X : ℝ} (hX : 0 < X)
    (k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (hh : X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (k a).val)) :
    scaleFirstPrimeTuplePiece i j ℓ ξ Ct H X k = largePrimeTuplePiece i j ℓ ξ Ct H X k := by
  unfold scaleFirstPrimeTuplePiece largePrimeTuplePiece
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rw [uncutPrimeTupleTerm_smoothed,largePrimeTupleTerm_high_box ℓ ξ Ct H hX k hh hq]

def scaleFirstHighSum (i j : ℕ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
      scaleFirstPrimeTuplePiece i j 0 ξ Ct H X d else 0

lemma scaleFirstHighSum_split (i j : ℕ) (ξ : ℝ) (Ct : ℕ) (H : ℝ)
    {X : ℝ} (hX : 1 ≤ X) :
    scaleFirstHighSum i j ξ Ct H X =
      largePrimeTupleHighSum i j ξ Ct H X + scaleFirstMiddleSum i j ξ Ct H X := by
  unfold scaleFirstHighSum largePrimeTupleHighSum scaleFirstMiddleSum
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hh : X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val)
  · have hn : X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) :=
      (Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (69/200:ℝ) ≤ 38/100)).trans hh
    simp only [hh,hn,not_lt_of_ge hh,and_false,ite_true,ite_false,add_zero]
    exact scaleFirstPrimeTuplePiece_eq_high i j 0 ξ Ct H (zero_lt_one.trans_le hX) d hh
  · by_cases hn : X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val)
    · simp only [hh,hn,lt_of_not_ge hh,and_self,ite_true,ite_false,zero_add]
    · simp only [hh,hn,false_and,ite_false,zero_add]

theorem scaleFirstHighSum_isLittleO (i j : ℕ)
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop, 0 < H X) :
    (fun X => scaleFirstHighSum i j ξ Ct (H X) X) =o[atTop] firstMomentScale := by
  have hh := largePrimeTupleHighSum_isLittleO i j hpnt hSW hpub hHuxley hperiod hMV hC
    hξ hξz (by norm_num : (0:ℝ) < 1/100) (by norm_num : (1/100:ℝ) ≤ 1/12)
    hGI hGQ hVor hGamma Ct H hH
  have hm := scaleFirstMiddleSum_isLittleO i j hSW hpub hHuxley hperiod hMV hC
    hξ hξz hGI hGQ hVor hGamma Ct H hH
  apply (hh.add hm).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (1:ℝ)] with X hX
  exact (scaleFirstHighSum_split i j ξ Ct (H X) hX).symm

end CubicFirstMoment

end

end OAI
