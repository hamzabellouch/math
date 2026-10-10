import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstHighSum
import OAI.NumberTheory.CubicMoment.Angular.AngularScaleFirstMiddleSum
import OAI.NumberTheory.CubicMoment.Angular.AngularLargeTupleHighSum

namespace OAI

/-! The high-scale branch is negligible. The middle interval is treated
by its distinguished group; the higher interval is the large-row high sum. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

def angular_scaleFirstHighSum (i j : ℕ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
      scaleFirstPrimeTuplePiece i j ℓ ξ Ct H X d else 0

lemma angular_scaleFirstHighSum_split (i j : ℕ) (ξ : ℝ) (Ct : ℕ) (H : ℝ)
    {X : ℝ} (hX : 1 ≤ X) :
    angular_scaleFirstHighSum ℓ i j ξ Ct H X =
      angular_largePrimeTupleHighSum ℓ i j ξ Ct H X + angular_scaleFirstMiddleSum ℓ i j ξ Ct H X := by
  unfold angular_scaleFirstHighSum angular_largePrimeTupleHighSum angular_scaleFirstMiddleSum
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hh : X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val)
  · have hn : X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) :=
      (Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (69/200:ℝ) ≤ 38/100)).trans hh
    simp only [hh,hn,not_lt_of_ge hh,and_false,ite_true,ite_false,add_zero]
    exact scaleFirstPrimeTuplePiece_eq_high i j ℓ ξ Ct H (zero_lt_one.trans_le hX) d hh
  · by_cases hn : X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val)
    · simp only [hh,hn,lt_of_not_ge hh,and_self,ite_true,ite_false,zero_add]
    · simp only [hh,hn,false_and,ite_false,zero_add]

theorem angular_scaleFirstHighSum_isLittleO (i j : ℕ)
    (hpnt : PrimaryPrimePNT) (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop, 0 < H X) :
    (fun X => angular_scaleFirstHighSum ℓ i j ξ Ct (H X) X) =o[atTop] firstMomentScale := by
  have hh := angular_largePrimeTupleHighSum_isLittleO ℓ i j hpnt hSW hℓ hpub hHuxley hperiod hMV hC
    hξ hξz (by norm_num : (0:ℝ) < 1/100) (by norm_num : (1/100:ℝ) ≤ 1/12)
    hGI hGQ hVor hGamma Ct H hH
  have hm := angular_scaleFirstMiddleSum_isLittleO ℓ i j hSW hℓ hpub hHuxley hperiod hMV hC
    hξ hξz hGI hGQ hVor hGamma Ct H hH
  apply (hh.add hm).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (1:ℝ)] with X hX
  exact (angular_scaleFirstHighSum_split ℓ i j ξ Ct (H X) hX).symm

end CubicFirstMoment

end

end OAI
