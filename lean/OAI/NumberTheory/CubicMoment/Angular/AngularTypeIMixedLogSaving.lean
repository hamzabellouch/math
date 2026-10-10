import OAI.NumberTheory.CubicMoment.Angular.AngularTypeIMixedFull
import OAI.NumberTheory.CubicMoment.Angular.AngularHeightCoefficient
import OAI.NumberTheory.CubicMoment.Angular.AngularDispersionModelEnergy
import OAI.NumberTheory.CubicMoment.Angular.AngularDispersionAbsoluteModel
import OAI.NumberTheory.CubicMoment.Estimates.TypeIMixedScale
import OAI.NumberTheory.CubicMoment.Angular.AngularDispersionModelNorm
import OAI.NumberTheory.CubicMoment.Estimates.MixedTermIdentity
import OAI.NumberTheory.CubicMoment.Estimates.UniformCoreBlockMoment

namespace OAI

/-! The actual Type-I mixed-term error after multiplication by the
correction polynomial. Its power saving implies every logarithmic saving. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_logarithmic_typeI_corrected_mixed
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {γ : Type*} {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {R₀ : ℝ} (hR₀ : 1 ≤ R₀)
    (hlo : ∀ j i x, x < 1 → W j i x = 0) (hhi : ∀ j i x, R₀ < x → W j i x = 0)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVp : tsupport V ⊆ Set.Ioi 0)
    (hVs : ContDiff ℝ ∞ V)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6)) (k : ℕ) :
    ∃ K T₀ : ℝ, 0 < K ∧ ∀ (j : γ) (Xi : ι → ℝ) (e : Eisenstein) (t A : ℝ),
      T₀ ≤ L j → 1 ≤ L j → (∀ i, 1 ≤ Xi i) → (∏ i, Xi i) = L j → L j^(99/100:ℝ) ≤ A →
      let S := fullSquarefreePrimeSupport R₀ (W j) Xi e
      let β := angularHeightPrimeCoefficient ℓ R₀ (W j) Xi
      ‖((cStar:ℂ)*star (dispersionModel S β t))*
        ((∑ b ∈ S, β b*normTwist t b*typeIMixedGauss b V A)-mixedMassModel S β t V A)‖ ≤
        K*A^(2/3:ℝ)*(L j)^(5/3:ℝ)/(1+Real.log (L j))^k := by
  let hv : UniformLogWeights (fun _ : Unit => V) := uniformLogWeights_constant V hVc hVp hVs
  let B := Real.exp hv.radius
  have hB : 1 ≤ B := Real.one_le_exp hv.radius_nonneg
  obtain ⟨J,hJ⟩ := pow_unbounded_of_one_lt (R₀^Fintype.card ι) (by norm_num : (1:ℝ) < 2)
  obtain ⟨K,hK,hbound⟩ := angular_logarithmic_prime_typeI_mixed_full ℓ hV hW hv hGamma hB J hJ
  obtain ⟨M,m,hM,hmodel⟩ := angular_logarithmic_dispersionModel_norm ℓ hW hR₀ hlo hhi
  obtain ⟨T₁,hT₁⟩ := eventually_atTop.mp (eventually_typeIMixed_dilation ((2:ℝ)^J))
  obtain ⟨T₂,hT₂⟩ := eventually_atTop.mp (negative_power_log_saving (by norm_num : (0:ℝ) < 1/100) (m+k))
  have hcs := cStar_pos
  let C := cStar*M*K
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C+1,max 2 (max B (max T₁ T₂)),by positivity,?_⟩
  intro j Xi e t A hT hL hXi hprod hA
  dsimp only
  let S := fullSquarefreePrimeSupport R₀ (W j) Xi e
  let β := angularHeightPrimeCoefficient ℓ R₀ (W j) Xi
  have hLp : 0 < L j := zero_lt_one.trans_le hL
  have hAp : 0 < A := (Real.rpow_pos_of_pos hLp _).trans_le hA
  have hA1 : 1 ≤ A := (Real.one_le_rpow hL (by norm_num : (0:ℝ) ≤ 99/100)).trans hA
  have hL2 : 2 ≤ L j := (le_max_left _ _).trans hT
  have hLB : B ≤ L j := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hLT₁ : T₁ ≤ L j := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hT))
  have hLT₂ : T₂ ≤ L j := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hT))
  have hLA : L j ≤ L j*A := le_mul_of_one_le_right hLp.le hA1
  have hcut (b : Eisenstein) (_hb : b ∈ S) (x : ℝ) (hx : B < x) : V x = 0 := by
    by_contra hn
    exact (not_le_of_gt hx) (hv.annular_support () (subset_tsupport V hn)).2
  have hb := hbound j Xi e (fun _ => ()) t A hL
    (fun i => zero_lt_one.trans_le (hXi i)) hprod (hlo j) (hhi j) hA1
    (hL2.trans hLA) (hLB.trans hLA) (hT₁ _ hLT₁ A hA) hcut
  have he : (∑ b ∈ S, (β b*normTwist t b)*(typeIMixedGauss b V A-typeIMixedModel b V A)) =
      (∑ b ∈ S, β b*normTwist t b*typeIMixedGauss b V A)-mixedMassModel S β t V A := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,typeIMixedModel_sum_eq]
  change ‖((cStar:ℂ)*star (dispersionModel S β t))*_‖ ≤ _
  rw [←he,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos cStar_pos,norm_star]
  have hz : 0 < 1+Real.log (L j) := by linarith [Real.log_nonneg hL]
  have hlog : (1+Real.log (L j))^m*(L j*A)^(-(1/100):ℝ) ≤ 1/(1+Real.log (L j))^k := by
    apply (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hLp hLA (by norm_num : -(1/100:ℝ) ≤ 0))
      (pow_nonneg hz.le _)).trans
    apply (mul_le_mul_of_nonneg_left (hT₂ (L j) hLT₂) (pow_nonneg hz.le m)).trans_eq
    rw [pow_add]
    field_simp
  calc
    _ ≤ (cStar*(M*(L j)^(5/6:ℝ)*(1+Real.log (L j))^m))*(K*A^(-1/6:ℝ)*(L j*A)^(5/6-1/100:ℝ)) := by
      apply mul_le_mul _ hb (_root_.norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left (hmodel j Xi e t hL hXi hprod) cStar_pos.le
    _ = C*(A^(2/3:ℝ)*(L j)^(5/3:ℝ))*((1+Real.log (L j))^m*(L j*A)^(-(1/100):ℝ)) := by
      calc
        _ = C*(A^(-1/6:ℝ)*(L j)^(5/6:ℝ)*(L j*A)^(5/6-1/100:ℝ))*(1+Real.log (L j))^m := by
          dsimp [C]
          ring
        _ = C*(A^(2/3:ℝ)*(L j)^(5/3:ℝ)*(L j*A)^(-(1/100):ℝ))*(1+Real.log (L j))^m := by
          rw [typeIMixed_scale_identity hAp hLp (1/100)]
        _ = _ := by ring
    _ ≤ C*(A^(2/3:ℝ)*(L j)^(5/3:ℝ))*(1/(1+Real.log (L j))^k) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ (C+1)*A^(2/3:ℝ)*(L j)^(5/3:ℝ)/(1+Real.log (L j))^k := by
      calc
        _ = C*(A^(2/3:ℝ)*(L j)^(5/3:ℝ)/(1+Real.log (L j))^k) := by ring
        _ ≤ (C+1)*(A^(2/3:ℝ)*(L j)^(5/3:ℝ)/(1+Real.log (L j))^k) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = _ := by ring

end CubicFirstMoment

end

end OAI
