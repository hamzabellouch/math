import OAI.NumberTheory.CubicMoment.Decomposition.StoppedMixedTypeI
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedMixedScale
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedModelNorm
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedMellinRows
import OAI.NumberTheory.CubicMoment.Estimates.MixedTermIdentity
import OAI.NumberTheory.CubicMoment.Estimates.UniformCoreBlockMoment

namespace OAI

/-! The mixed-term error for the stopped coefficient.
The product-squarefree model is retained; the remaining model-coprimality
comparison belongs to the variance assembly. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_corrected_mixed_log_saving
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVp : tsupport V ⊆ Set.Ioi 0)
    (hVs : ContDiff ℝ ∞ V)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    {ξ κ : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) →
      ∀ (selected : Eisenstein → Eisenstein → Prop) (e : Eisenstein) (b A u : ℝ),
      X^κ ≤ b → b ≤ X → b^(3/2:ℝ) ≤ A →
      let S := stoppedIntervalSupport ι X (b/2) b e
      let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W selected
      ‖((cStar:ℂ)*star (dispersionModel S β u))*
        ((∑ r ∈ S, β r*normTwist u r*typeIMixedGauss r V A)-mixedMassModel S β u V A)‖ ≤
        K*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k := by
  let hw : UniformLogWeights (fun _ : Unit => V) := uniformLogWeights_constant V hVc hVp hVs
  let B := Real.exp hw.radius
  have hB : 1 ≤ B := Real.one_le_exp hw.radius_nonneg
  obtain ⟨K,hK,htype⟩ := stopped_typeI_mixed (ι := ι) hV hw hGamma hB hξ hξz
  obtain ⟨D,hD,hmodel⟩ := stopped_model_norm (ι := ι) hξ hξz
  have hcStar : 0 < cStar := cStar_pos
  let E := cStar*D*K
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨E+1,by positivity,?_⟩
  filter_upwards [htype,hmodel,
    (tendsto_rpow_atTop hκ).eventually_ge_atTop (max 2 (2*B)),
    negative_power_log_saving (show 0 < κ/100 by positivity) k,
    eventually_ge_atTop (Real.exp 1)] with X htype hmodel hlarge hdecay hX
  intro W hW selected e b A u hb hbX hAlo
  let S := stoppedIntervalSupport ι X (b/2) b e
  let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W selected
  have hb2 : 2 ≤ b := ((le_max_left _ _).trans hlarge).trans hb
  have hBb : 2*B ≤ b := ((le_max_right _ _).trans hlarge).trans hb
  have hbp : 0 < b := by linarith
  obtain ⟨hA1,hprod,hlevel⟩ := stopped_mixed_level hb2 hAlo
  have hAp : 0 < A := zero_lt_one.trans_le hA1
  have hBA : B ≤ (b/2)*A := by
    have hh := le_mul_of_one_le_right (show 0 ≤ b/2 by positivity) hA1
    linarith
  have hcut (r : Eisenstein) (_hr : r ∈ S) (x : ℝ) (hx : B < x) : V x = 0 := by
    by_contra hn
    exact (not_le_of_gt hx) (hw.annular_support () (subset_tsupport V hn)).2
  have ht := htype W hW selected e (fun _ => ()) b A u hb2 hbX hA1 hprod hBA hlevel hcut
  have hphase (r : Eisenstein) : stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W selected r =
      β r*normTwist u r := by
    rw [stoppedRowCoefficient_phase,normTwist_eq_mellinPhase]
  have heq : (∑ r ∈ S, stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W selected r*
      (typeIMixedGauss r V A-typeIMixedModel r V A)) =
      (∑ r ∈ S, β r*normTwist u r*typeIMixedGauss r V A)-mixedMassModel S β u V A := by
    simp_rw [hphase,mul_sub]
    rw [Finset.sum_sub_distrib,typeIMixedModel_sum_eq]
  change ‖∑ r ∈ S, stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W selected r*
    (typeIMixedGauss r V A-typeIMixedModel r V A)‖ ≤ _ at ht
  rw [heq] at ht
  have ht' : ‖(∑ r ∈ S, β r*normTwist u r*typeIMixedGauss r V A)-mixedMassModel S β u V A‖ ≤
      K*A^(-1/6:ℝ)*(b*A)^(5/6-1/100:ℝ) := ht.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
      (by nlinarith) (by norm_num)) (by positivity))
  have hX1 : 1 ≤ X := (Real.one_le_exp_iff.mpr (by norm_num)).trans hX
  have hXp : 0 < X := zero_lt_one.trans_le hX1
  have hz : 0 < Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 1) hX
    rw [Real.log_exp] at hh
    linarith
  have hsmall : (b*A)^(-(1/100):ℝ) ≤ 1/(Real.log X)^k := by
    have hba : b ≤ b*A := le_mul_of_one_le_right hbp.le hA1
    have h₁ := Real.rpow_le_rpow_of_nonpos hbp hba (by norm_num : -(1/100:ℝ) ≤ 0)
    have h₂ := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hXp κ) hb
      (by norm_num : -(1/100:ℝ) ≤ 0)
    rw [←Real.rpow_mul hXp.le] at h₂
    have he : κ*(-(1/100:ℝ)) = -(κ/100) := by ring
    rw [he] at h₂
    exact ((h₁.trans h₂).trans hdecay).trans
      (one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hz.le (by linarith) k))
  change ‖((cStar:ℂ)*star (dispersionModel S β u))*_‖ ≤ _
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos cStar_pos,norm_star]
  calc
    _ ≤ (cStar*(D*b^(5/6:ℝ)))*(K*A^(-1/6:ℝ)*(b*A)^(5/6-1/100:ℝ)) := by
      apply mul_le_mul _ ht' (_root_.norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left (hmodel W hW selected e b 0 u hbp hbX) cStar_pos.le
    _ = E*(A^(2/3:ℝ)*b^(5/3:ℝ))*(b*A)^(-(1/100):ℝ) := by
      calc
        _ = E*(A^(-1/6:ℝ)*b^(5/6:ℝ)*(b*A)^(5/6-1/100:ℝ)) := by dsimp [E]; ring
        _ = _ := by rw [typeIMixed_scale_identity hAp hbp (1/100)]; ring
    _ ≤ E*(A^(2/3:ℝ)*b^(5/3:ℝ))*(1/(Real.log X)^k) :=
      mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = E*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k := by ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : E ≤ E+1)
          (Real.rpow_nonneg hAp.le _)) (Real.rpow_nonneg hbp.le _))
      (pow_nonneg hz.le _)

end CubicFirstMoment

end

end OAI
