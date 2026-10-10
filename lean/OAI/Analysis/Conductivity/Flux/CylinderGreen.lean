import Mathlib
import OAI.Analysis.Conductivity.Variational.AxialDecayL2

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus

local instance cylinderGreenMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance cylinderGreenProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma poisson_complex_hermitian_green {q : ℝ → ℂ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (m R : ℝ) (a : ℂ) :
    (∫ t in (0:ℝ)..R,
      inner ℂ (axialDecayField m (-(m:ℂ)*a) t) (deriv q t) +
      (m^2:ℝ)*inner ℂ (axialDecayField m a t) (q t)) =
      (m:ℂ)*inner ℂ a (q 0)-(m*Real.exp (-m*R):ℝ)*inner ℂ a (q R) := by
  have he (t : ℝ) : HasDerivAt (fun t : ℝ => (Real.exp (-m*t):ℂ))
      ((Real.exp (-m*t)*(-m):ℝ):ℂ) t := by
    simpa only [id_eq,mul_one] using (((hasDerivAt_id t).const_mul (-m)).exp).ofReal_comp
  have hd (t : ℝ) : HasDerivAt
      (fun t : ℝ => (-(m:ℂ)*(Real.exp (-m*t):ℂ)*starRingEnd ℂ a)*q t)
      (inner ℂ (axialDecayField m (-(m:ℂ)*a) t) (deriv q t) +
        (m^2:ℝ)*inner ℂ (axialDecayField m a t) (q t)) t := by
    convert! (((he t).const_mul (-(m:ℂ))).mul_const (starRingEnd ℂ a)).mul
      ((hq.differentiable (by simp) t).hasDerivAt) using 1
    simp only [axialDecayField,RCLike.inner_apply,map_mul,map_neg,Complex.conj_ofReal,
      Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_pow]
    ring
  have hc : Continuous (fun t : ℝ =>
      inner ℂ (axialDecayField m (-(m:ℂ)*a) t) (deriv q t) +
        (m^2:ℝ)*inner ℂ (axialDecayField m a t) (q t)) := by
    exact ((axialDecayField_continuous _ _).inner (hq.continuous_deriv (by simp))).add
      (continuous_const.mul ((axialDecayField_continuous _ _).inner hq.continuous))
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (hc.intervalIntegrable 0 R)
  rw [H]
  simp only [mul_zero,Real.exp_zero,Complex.ofReal_one,mul_one,RCLike.inner_apply,
    Complex.ofReal_mul]
  ring

lemma smoothFiniteAxis_memLp {q : ℝ → ℂ} (hq : Continuous q) (R : ℝ) :
    MemLp q 2 (FiniteAxisMeasure R) := by
  apply (memLp_two_iff_integrable_sq_norm hq.aestronglyMeasurable).mpr
  exact (hq.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self

def smoothFiniteAxisLp {q : ℝ → ℂ} (hq : Continuous q) (R : ℝ) : FiniteAxisL2 R :=
  (smoothFiniteAxis_memLp hq R).toLp q

lemma smoothFiniteAxisLp_ae {q : ℝ → ℂ} (hq : Continuous q) (R : ℝ) :
    smoothFiniteAxisLp hq R=ᵐ[FiniteAxisMeasure R] q :=
  (smoothFiniteAxis_memLp hq R).coeFn_toLp

lemma finiteDecay_green_inner {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q)
    (m R : ℝ) (hR : 0≤R) (a : ℂ) :
    inner ℂ (finiteDecayLp m R (-(m:ℂ)*a)) (smoothFiniteAxisLp (hq.continuous_deriv (by simp)) R)+
      (m^2:ℝ)*inner ℂ (finiteDecayLp m R a) (smoothFiniteAxisLp hq.continuous R)=
      (m:ℂ)*inner ℂ a (q 0)-(m*Real.exp (-m*R):ℝ)*inner ℂ a (q R) := by
  have h1 := L2.integrable_inner (𝕜:=ℂ) (finiteDecayLp m R (-(m:ℂ)*a))
    (smoothFiniteAxisLp (hq.continuous_deriv (by simp)) R)
  have h2 := L2.integrable_inner (𝕜:=ℂ) (finiteDecayLp m R a) (smoothFiniteAxisLp hq.continuous R)
  rw [L2.inner_def,L2.inner_def,←integral_const_mul,←integral_add h1 (h2.const_mul _)]
  have he : (∫ t,inner ℂ (finiteDecayLp m R (-(m:ℂ)*a) t)
      (smoothFiniteAxisLp (hq.continuous_deriv (by simp)) R t)+
      (m^2:ℝ)*inner ℂ (finiteDecayLp m R a t) (smoothFiniteAxisLp hq.continuous R t)
      ∂FiniteAxisMeasure R)=
      ∫ t in Ioc (0:ℝ) R,inner ℂ (axialDecayField m (-(m:ℂ)*a) t) (deriv q t)+
      (m^2:ℝ)*inner ℂ (axialDecayField m a t) (q t) := by
    apply integral_congr_ae
    filter_upwards [finiteDecayLp_ae m R (-(m:ℂ)*a),finiteDecayLp_ae m R a,
      smoothFiniteAxisLp_ae (hq.continuous_deriv (by simp)) R,smoothFiniteAxisLp_ae hq.continuous R]
      with t h1 h2 h3 h4
    rw [h1,h2,h3,h4]
  rw [he,←intervalIntegral.integral_of_le hR]
  exact poisson_complex_hermitian_green hq m R a

end ScalarConductivity

end

end OAI
