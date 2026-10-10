import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Estimates.OutgoingPower2
import OAI.MeasureTheory.FalconerCompletion.Measures.GaussianMomentFlow2
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereCasimir2

namespace OAI

/-! Canonical spherical measures and differential identities. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open MeasureTheory Set Filter
open scoped ContDiff RealInnerProductSpace SchwartzMap FourierTransform Topology
variable {n : ℕ}

abbrev SphereAmbientND (n : ℕ) := WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)

structure NorthAmplitudeND (n : ℕ) where
  toFun : SphereAmbientND n → ℂ
  smooth : ContDiff ℝ ∞ toFun
  support : tsupport toFun ⊆ {w | -(1/2:ℝ) ≤ (WithLp.ofLp w).2}

instance : CoeFun (NorthAmplitudeND n) (fun _ => SphereAmbientND n → ℂ) := ⟨NorthAmplitudeND.toFun⟩

noncomputable def sphereBasisND (n : ℕ) := stdOrthonormalBasis ℝ (SphereAmbientND n)

lemma finrank_sphereAmbientND : Module.finrank ℝ (SphereAmbientND n) = n+1 := by
  rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq,Module.finrank_prod]
  simp

noncomputable def NorthAmplitudeND.casimir (b : NorthAmplitudeND n) : NorthAmplitudeND n where
  toFun := sphereCasimirND (sphereBasisND n) b
  smooth := sphereCasimirND_contDiff _ b.smooth
  support := (tsupport_sphereCasimirND_subset _ _).trans b.support

lemma northAmplitudeND_vanish (b : NorthAmplitudeND n) (w : SphereAmbientND n)
    (hw : (WithLp.ofLp w).2 ≤ 1-(Real.sqrt (7/2:ℝ))^2/2) : b w = 0 := by
  have hs : (Real.sqrt (7/2:ℝ))^2 = 7/2 := Real.sq_sqrt (by norm_num)
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have hz := b.support h
  change -(1/2:ℝ) ≤ (WithLp.ofLp w).2 at hz
  rw [hs] at hw
  linarith

lemma sqrt_seven_halves_lt_two : Real.sqrt (7/2:ℝ) < 2 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 7/2 by norm_num),Real.sqrt_nonneg (7/2:ℝ)]

noncomputable def NorthAmplitudeND.chart (b : NorthAmplitudeND n) :
    𝓢(EuclideanSpace ℝ (Fin n),ℂ) :=
  sphereChartSchwartzND b (Real.sqrt (7/2:ℝ)) (Real.sqrt_nonneg _)
    sqrt_seven_halves_lt_two b.smooth (fun w _ h => northAmplitudeND_vanish b w h)

noncomputable def NorthAmplitudeND.profile (b : NorthAmplitudeND n) (h : ℝ) : ℂ :=
  gaussianMomentFlowND (𝓕⁻ b.chart) 0 (2*Real.pi^2*h)

lemma NorthAmplitudeND.profile_smooth (b : NorthAmplitudeND n) :
    ContDiff ℝ ∞ b.profile :=
  (gaussianMomentFlowND_contDiff (𝓕⁻ b.chart) 0).comp (by fun_prop)

noncomputable def sphereLeadingND (n : ℕ) : ℂ :=
  ((2*Real.pi)^(n/2:ℝ):ℝ)*Complex.exp (-(Real.pi:ℂ)*n/4*Complex.I)

lemma sphereLeadingND_ne_zero (n : ℕ) : sphereLeadingND n ≠ 0 := by
  apply mul_ne_zero _ (Complex.exp_ne_zero _)
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _))

lemma fresnelCoefficientND_half {s : ℝ} (hs : 0 < s) :
    fresnelCoefficientND (EuclideanSpace ℝ (Fin n)) (s/2) =
      sphereLeadingND n * (s^(-(n/2:ℝ)) : ℝ) := by
  unfold fresnelCoefficientND sphereLeadingND
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  have he : Real.pi/(s/2) = (2*Real.pi)/s := by ring
  rw [he,Real.div_rpow (by positivity) hs.le,Real.rpow_neg hs.le]
  push_cast
  ring

lemma NorthAmplitudeND.integral_profile (b : NorthAmplitudeND n) {s : ℝ} (hs : 0 < s) :
    sphereAxisIntegralND s (WithLp.toLp 2 (0,(1:ℝ))) b =
      outgoingProfileND (n/2:ℝ) (sphereLeadingND n) b.profile s := by
  have hQ := integral_sphereAreaND_eq_quadratic (Real.sqrt_nonneg (7/2:ℝ))
    sqrt_seven_halves_lt_two b.smooth.continuous.stronglyMeasurable
    (fun w _ h => northAmplitudeND_vanish b w h) s
  change sphereAxisIntegralND s (WithLp.toLp 2 (0,(1:ℝ))) b = _ at hQ
  rw [hQ]
  change Complex.exp (Complex.I*s) *
    (∫ u : EuclideanSpace ℝ (Fin n),
      Complex.exp (-(((s/2:ℝ):ℂ)*Complex.I)*(‖u‖:ℂ)^2)*b.chart u) = _
  rw [quadratic_stationaryND_identity (by positivity),fresnelCoefficientND_half hs]
  unfold outgoingProfileND outgoingPowerND NorthAmplitudeND.profile gaussianMomentFlowND
  simp only [Nat.mul_zero,pow_zero,mul_one]
  have he : Real.pi^2/(s/2) = 2*Real.pi^2*s⁻¹ := by ring
  rw [he]
  ring

lemma outgoingPowerND_ne_zero (α : ℝ) {c : ℂ} (hc : c ≠ 0) {s : ℝ} (hs : 0 < s) :
    outgoingPowerND α c s ≠ 0 := by
  apply mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) hc)
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos hs _))

lemma NorthAmplitudeND.profile_zero (b : NorthAmplitudeND n) :
    b.profile 0 = b (WithLp.toLp 2 (0,(1:ℝ))) := by
  have hm := schwartz_inverseND_even_moment b.chart 0
  simp only [Nat.mul_zero,pow_zero,one_mul,inv_one,iteratedLaplacianND] at hm
  unfold NorthAmplitudeND.profile gaussianMomentFlowND
  simp only [mul_zero,zero_mul,Complex.ofReal_zero,Complex.exp_zero,one_mul,pow_zero]
  rw [hm]
  change sphereChartAmplitudeND b 0 = _
  simp [sphereChartAmplitudeND,sphereChartWeightND,sphereChartND_north,sphereChartScaleND]

lemma NorthAmplitudeND.profile_helmholtz (b : NorthAmplitudeND n) {t : ℝ} (ht : 0 < t) :
    b.casimir.profile t = ((n/2:ℝ):ℂ)*((n/2:ℝ)-1)*b.profile t +
      2*Complex.I*deriv b.profile t - 2*(t:ℂ)*deriv b.profile t -
      (t:ℂ)^2*deriv (deriv b.profile) t := by
  let e : SphereAmbientND n := WithLp.toLp 2 (0,(1:ℝ))
  have he : ‖e‖ = 1 := sphere_north_normND
  have heq : EqOn (fun s => sphereAxisIntegralND s e b)
      (outgoingProfileND (n/2:ℝ) (sphereLeadingND n) b.profile) (Ioi 0) :=
    fun s hs => b.integral_profile hs
  have hd₁ := heq.deriv isOpen_Ioi
  have hd₂ := hd₁.deriv isOpen_Ioi
  have hs : 0 < t⁻¹ := inv_pos.mpr ht
  have hO := sphereAxisIntegralND_helmholtz (sphereBasisND n) t⁻¹ he b.smooth
  change sphereAxisIntegralND t⁻¹ e b.casimir = _ at hO
  have h₁ := hd₁ hs
  have h₂ := hd₂ hs
  rw [b.casimir.integral_profile hs,b.integral_profile hs,h₁,h₂] at hO
  have hdim : ((Fintype.card (Fin (Module.finrank ℝ (SphereAmbientND n))):ℂ)-1) =
      2*((n/2:ℝ):ℂ) := by
    rw [Fintype.card_fin,finrank_sphereAmbientND]
    push_cast
    ring
  rw [hdim] at hO
  have hH := b.profile_smooth.differentiable (by simp)
  have hH' := (smooth_deriv_complexND b.profile_smooth).differentiable (by simp)
  have hP := radialHelmholtz_outgoingProfileND hH hH' hs (α := (n/2:ℝ))
      (c := sphereLeadingND n)
  rw [hP] at hO
  unfold outgoingProfileND at hO
  have hK := outgoingPowerND_ne_zero (n/2:ℝ) (sphereLeadingND_ne_zero n) hs
  have hh := mul_left_cancel₀ hK hO
  simpa only [inv_inv,Complex.ofReal_inv] using hh

lemma NorthAmplitudeND.profile_jets (b : NorthAmplitudeND n) (j : ℕ) :
    2*Complex.I*iteratedDeriv (j+1) b.profile 0 =
      iteratedDeriv j b.casimir.profile 0 +
      ((j:ℂ)*(j+1)-((n/2:ℝ):ℂ)*((n/2:ℝ)-1))*iteratedDeriv j b.profile 0 :=
  helmholtz_profile_jetsND b.profile_smooth b.casimir.profile_smooth
    ((n/2:ℝ):ℂ) (fun _ ht => b.profile_helmholtz ht) j

noncomputable def sphereJetPolynomialND (n : ℕ) : ℕ → (SphereAmbientND n → ℂ) → SphereAmbientND n → ℂ
  | 0, b => b
  | j+1, b => fun w => sphereJetPolynomialND n j (sphereCasimirND (sphereBasisND n) b) w +
      ((j:ℂ)*(j+1)-((n/2:ℝ):ℂ)*((n/2:ℝ)-1))*sphereJetPolynomialND n j b w

lemma NorthAmplitudeND.profile_jets_polynomial (b : NorthAmplitudeND n) (j : ℕ) :
    (2*Complex.I)^j * iteratedDeriv j b.profile 0 =
      sphereJetPolynomialND n j b (WithLp.toLp 2 (0,(1:ℝ))) := by
  induction j generalizing b with
  | zero => simpa [sphereJetPolynomialND] using b.profile_zero
  | succ j ih =>
    rw [pow_succ,mul_assoc,b.profile_jets]
    rw [mul_add,ih b.casimir]
    rw [mul_left_comm,ih b]
    rfl

lemma NorthAmplitudeND.profile_jets_moments (b : NorthAmplitudeND n) (j : ℕ) :
    iteratedDeriv j b.profile 0 =
      (2*(Real.pi:ℂ)^2)^j*Complex.I^j *
        ∫ ξ : EuclideanSpace ℝ (Fin n), (‖ξ‖:ℂ)^(2*j)*𝓕⁻ b.chart ξ := by
  unfold NorthAmplitudeND.profile
  rw [iteratedDeriv_comp_const_smul
    ((gaussianMomentFlowND_contDiff (𝓕⁻ b.chart) 0).of_le (nat_cast_le_inftyND _)),
    gaussianMomentFlowND_iteratedDeriv]
  simp only [mul_zero,Nat.zero_add,gaussianMomentFlowND,zero_mul,Complex.ofReal_zero,
    Complex.exp_zero,one_mul,Complex.real_smul]
  push_cast
  ring

lemma NorthAmplitudeND.quadratic_series_global (b : NorthAmplitudeND n) (J : ℕ)
    {s : ℝ} (hs : 0 < s) :
    quadraticExpansionND b.chart J (s/2) =
      ∑ j ∈ Finset.range (J+1),
        ((s:ℂ)^j * (2*Complex.I)^j * (j.factorial:ℂ))⁻¹ *
          sphereJetPolynomialND n j b (WithLp.toLp 2 (0,(1:ℝ))) := by
  unfold quadraticExpansionND
  apply Finset.sum_congr rfl
  intro j hj
  rw [← b.profile_jets_polynomial j,b.profile_jets_moments]
  have hsC : (s:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hf : (j.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hi : 2*Complex.I ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  push_cast
  simp only [div_eq_mul_inv,mul_pow]
  field_simp [hsC,hf,hi,← inv_pow]
  ring_nf
  rw [← mul_pow,mul_inv_cancel₀ hsC,one_pow,one_mul]

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
