import Mathlib
import OAI.Probability.SKSupport.Density.GaussianTails

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.Heat

def gaussianLogDensity (d : ℝ) (U : ℝ → ℝ) (x : ℝ) := Real.exp (-d*x^2+U x)

lemma gaussianLogDensity_continuous {U : ℝ → ℝ} (hU : Continuous U) (d : ℝ) :
    Continuous (gaussianLogDensity d U) := by unfold gaussianLogDensity;fun_prop

lemma gaussianLogDensity_pos (d : ℝ) (U : ℝ → ℝ) (x : ℝ) : 0 < gaussianLogDensity d U x := Real.exp_pos _

lemma gaussianLogDensity_even {U : ℝ → ℝ} (hU : Function.Even U) (d : ℝ) :
    Function.Even (gaussianLogDensity d U) := by intro x;simp only [gaussianLogDensity,neg_sq,hU x]

lemma gaussianLogDensity_derivative {U : ℝ → ℝ} {d x U' : ℝ} (hU : HasDerivAt U U' x) :
    HasDerivAt (gaussianLogDensity d U) ((U'-2*d*x)*gaussianLogDensity d U x) x := by
  convert (((hasDerivAt_id x).pow 2).const_mul (-d) |>.add hU).exp using 1 <;>
    first | rfl | (dsimp [gaussianLogDensity];ring)

lemma gaussianLogDensity_integrable_mul {U g : ℝ → ℝ} {K : ℝ≥0} (hU : LipschitzWith K U)
    (hgm : Measurable g) (hg : ExponentialBound g) {d : ℝ} (hd : 0 < d) :
    Integrable (fun x => gaussianLogDensity d U x*g x) := by
  have hE : ExponentialBound (fun x => Real.exp (U x)) := by simpa only [one_mul] using exponentialBound_exp hU 1
  have hh := integrable_gaussian_expBound (hU.continuous.measurable.exp.mul hgm) (hE.mul hg) hd
  simpa only [gaussianLogDensity,Real.exp_add,mul_assoc,Pi.mul_apply] using hh

lemma gaussianLogDensity_tendsto_mul {U g : ℝ → ℝ} {K : ℝ≥0} (hU : LipschitzWith K U)
    (hg : ExponentialBound g) {d : ℝ} (hd : 0 < d) :
    Tendsto (fun x => gaussianLogDensity d U x*g x) atTop (𝓝 0) := by
  have hE : ExponentialBound (fun x => Real.exp (U x)) := by simpa only [one_mul] using exponentialBound_exp hU 1
  simpa only [gaussianLogDensity,Real.exp_add,mul_assoc,Pi.mul_apply] using gaussian_expBound_tendsto_zero (hE.mul hg) hd

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma BoundedSmooth.pow {f : ℝ → ℝ} (hf : BoundedSmooth f) (n : ℕ) : BoundedSmooth (fun x => (f x)^n) := by
  induction n with
  | zero => simpa only [pow_zero] using BoundedSmooth.const 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

def coercivePolynomial (r : ℝ → ℝ) (x : ℝ) :=
  (certZ r x)^2-12*certV r x*(certW r x)^2+6*(certV r x)^4

def quarticMoment (r : ℝ → ℝ) (x : ℝ) := (certV r x)^4

lemma quarticMoment_boundedSmooth {r : ℝ → ℝ} (hr : BoundedSmooth r) : BoundedSmooth (quarticMoment r) := hr.deriv.pow 4

lemma coercivePolynomial_boundedSmooth {r : ℝ → ℝ} (hr : BoundedSmooth r) : BoundedSmooth (coercivePolynomial r) := by
  have hw : BoundedSmooth (certW r) := by simpa only [certW,iteratedDeriv_succ,iteratedDeriv_zero] using hr.deriv.deriv
  have hz : BoundedSmooth (certZ r) := by simpa only [certZ,iteratedDeriv_succ,iteratedDeriv_zero] using hr.deriv.deriv.deriv
  convert ((hz.pow 2).add ((hr.deriv.mul (hw.pow 2)).const_mul (-12))).add ((hr.deriv.pow 4).const_mul 6) using 1
  funext x
  dsimp [coercivePolynomial,certV]
  ring

lemma quarticMoment_even {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (ho : Function.Odd r) : Function.Even (quarticMoment r) := by
  intro x;simp only [quarticMoment,certV_even hr ho x]

lemma coercivePolynomial_even {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (ho : Function.Odd r) : Function.Even (coercivePolynomial r) := by
  intro x
  simp only [coercivePolynomial,certV_even hr ho x,certZ_even hr ho x,certW_odd hr ho x,neg_sq]

lemma integral_even_two_Ioi {f : ℝ → ℝ} (hf : Function.Even f) : (∫ x, f x)=2*∫ x in Ioi (0:ℝ), f x := by
  have he : (fun x => f |x|)=f := by
    funext x
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos (le_of_lt (lt_of_not_ge hx)),hf x]
  have hh := integral_comp_abs (f := f)
  rw [he] at hh
  exact hh

lemma certificate_polynomial_measurable {r s : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s) :
    Measurable (fun x => Certificate.WF₂ (certR r x) (certK r s x) (certV r x) (certB r x) (certJ r s x)
      (certZ r x) (certL r s x)) := by
  have hrm := hr.continuous.measurable
  have hsm := hs.continuous.measurable
  have hvm : Measurable (certV r) := (contDiff_infty_iff_deriv.mp hr |>.2).continuous.measurable
  have hwm : Measurable (certW r) := (contDiff_iteratedDeriv_infty hr 2).continuous.measurable
  have hzm : Measurable (certZ r) := (contDiff_iteratedDeriv_infty hr 3).continuous.measurable
  have hsdm : Measurable (deriv s) := (contDiff_infty_iff_deriv.mp hs |>.2).continuous.measurable
  have hssm : Measurable (iteratedDeriv 2 s) := (contDiff_iteratedDeriv_infty hs 2).continuous.measurable
  have hR : Measurable (certR r) := hrm.pow_const 2
  have hK : Measurable (certK r s) := hrm.mul hsm
  have hB : Measurable (certB r) := hwm.neg.div hrm
  have hJ : Measurable (certJ r s) := hsdm.sub ((hsm.div hrm).mul hvm)
  have hL : Measurable (certL r s) := hrm.neg.mul hssm
  dsimp only [Certificate.WF₂,Certificate.DF₂,Certificate.F₂R,Certificate.F₂K,Certificate.F₂v,
    Certificate.F₂b,Certificate.F₂j,Certificate.F₂,Certificate.F₁,Certificate.Q,Certificate.T]
  fun_prop

theorem gaussian_shape_coercivity {r s U : ℝ → ℝ} {K : ℝ≥0} {d : ℝ}
    (hr : BoundedSmooth r) (hs : RegularDatum s) (hshape : BackwardShape r)
    (hso : Function.Odd s) (hsa : ∀ x, 0 ≤ deriv s x)
    (hsw : ∀ x, 0 ≤ x → iteratedDeriv 2 s x ≤ 0)
    (hQ : ∀ x, 0 ≤ x → 0 ≤ r x*deriv s x-s x*deriv r x)
    (hU : LipschitzWith K U) (hUe : Function.Even U) (hd : 0 < d)
    (hUd : ∀ x, HasDerivAt U (r x-s x+2*d*x) x) :
    (1/1000:ℝ)*(∫ x, gaussianLogDensity d U x*quarticMoment r x) ≤
      ∫ x, gaussianLogDensity d U x*coercivePolynomial r x := by
  let ρ := gaussianLogDensity d U
  have hρ : Continuous ρ := gaussianLogDensity_continuous hU.continuous d
  have hρpos : ∀ x, 0 ≤ ρ x := fun x => (gaussianLogDensity_pos d U x).le
  have hρe : Function.Even ρ := gaussianLogDensity_even hUe d
  have hρd (x : ℝ) : HasDerivAt ρ ((r x-s x)*ρ x) x := by
    convert gaussianLogDensity_derivative (d := d) (hUd x) using 1
    first | rfl | ring
  obtain ⟨hF,hW⟩ := certificate_growth hr hs hshape hso
  have hiV : Integrable (fun x => ρ x*quarticMoment r x) :=
    gaussianLogDensity_integrable_mul hU (quarticMoment_boundedSmooth hr).smooth.continuous.measurable
      (quarticMoment_boundedSmooth hr).exponentialBound hd
  have hiP : Integrable (fun x => ρ x*coercivePolynomial r x) :=
    gaussianLogDensity_integrable_mul hU (coercivePolynomial_boundedSmooth hr).smooth.continuous.measurable
      (coercivePolynomial_boundedSmooth hr).exponentialBound hd
  have hiD : Integrable (certDivergence r s ρ) :=
    gaussianLogDensity_integrable_mul hU (certificate_polynomial_measurable hr.smooth hs.smooth) hW hd
  have htFlux : Tendsto (certFlux r s ρ) atTop (𝓝 0) := by
    unfold certFlux
    have hh := gaussianLogDensity_tendsto_mul hU (hr.exponentialBound.mul hF) hd
    simpa only [certFlux,ρ,Pi.mul_apply,mul_comm,mul_left_comm,mul_assoc] using hh
  have hiZero : (∫ x in Ioi (0:ℝ), certDivergence r s ρ x)=0 := by
    have hh := integral_Ioi_of_hasDerivAt_of_tendsto
      (cert_flux_continuous hr.smooth hs.smooth hshape hso hρ |>.continuousWithinAt (x := 0))
      (fun x hx => cert_flux_derivative hr.smooth hs.smooth (ne_of_gt (hshape.pos hx)) (hρd x))
      hiD.integrableOn htFlux
    simpa only [certFlux,hshape.zero,zero_mul,sub_zero] using hh
  have hhalf : (1661507/1521000000:ℝ)*(∫ x in Ioi (0:ℝ), ρ x*quarticMoment r x) ≤
      ∫ x in Ioi (0:ℝ), ρ x*coercivePolynomial r x := by
    have hm := integral_mono_ae ((hiV.const_mul (1661507/1521000000:ℝ)).add hiD).integrableOn hiP.integrableOn
      (show ∀ᵐ x ∂volume.restrict (Ioi (0:ℝ)),
        (1661507/1521000000:ℝ)*(ρ x*quarticMoment r x)+certDivergence r s ρ x ≤ ρ x*coercivePolynomial r x from by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          have hh := mul_le_mul_of_nonneg_left
            (cert_halfLine_coercive hr.smooth hs.smooth hshape hso hsa hsw hQ hx) (hρpos x)
          dsimp only [quarticMoment,coercivePolynomial,certDivergence]
          nlinarith only [hh])
    simp only [Pi.add_apply] at hm
    rw [integral_add (hiV.const_mul _).integrableOn hiD.integrableOn,integral_const_mul,hiZero,add_zero] at hm
    exact hm
  have hVe : Function.Even (fun x => ρ x*quarticMoment r x) := by
    intro x;dsimp only;rw [hρe x,quarticMoment_even hr.smooth hshape.odd x]
  have hPe : Function.Even (fun x => ρ x*coercivePolynomial r x) := by
    intro x;dsimp only;rw [hρe x,coercivePolynomial_even hr.smooth hshape.odd x]
  have hfull : (1661507/1521000000:ℝ)*(∫ x, ρ x*quarticMoment r x) ≤ ∫ x, ρ x*coercivePolynomial r x := by
    rw [integral_even_two_Ioi hVe,integral_even_two_Ioi hPe]
    nlinarith only [hhalf]
  exact (mul_le_mul_of_nonneg_right Certificate.coercivity_constant.le
    (integral_nonneg (fun x => mul_nonneg (hρpos x) (by exact pow_nonneg (le_of_lt (hshape.derivative_pos x)) 4)))).trans hfull

end ZeroTemperatureSK.Heat

end
end

end OAI
