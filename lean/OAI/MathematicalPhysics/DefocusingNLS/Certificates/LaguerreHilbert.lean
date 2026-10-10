import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ShiftedSlowGrowth
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Orthonormal

namespace OAI

/-! # Hilbert-space decay of Laguerre coefficients

Multiplication by `exp (-t/2)` puts the weighted problem into the ordinary
complex L² space on the positive ray. Bessel's inequality then proves decay
of coefficients without presupposing completeness of the Laguerre family.
-/

open Filter Topology MeasureTheory Set Asymptotics
open scoped ComplexConjugate

namespace DefocusingNLS

noncomputable def halfWeighted (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Real.exp (-t / 2) : ℂ) * f t

theorem halfWeighted_norm_sq (f : ℝ → ℂ) (t : ℝ) :
    ‖halfWeighted f t‖ ^ 2 = Real.exp (-t) * ‖f t‖ ^ 2 := by
  simp only [halfWeighted, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le, mul_pow]
  have h : Real.exp (-t / 2) ^ 2 = Real.exp (-t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [h]

theorem halfWeighted_inner (f g : ℝ → ℂ) (t : ℝ) :
    conj (halfWeighted f t) * halfWeighted g t =
      (Real.exp (-t) : ℂ) * conj (f t) * g t := by
  have h : (Real.exp (-t / 2) : ℂ) ^ 2 = (Real.exp (-t) : ℂ) := by
    norm_cast
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simp only [halfWeighted, map_mul, Complex.conj_ofReal]
  calc
    _ = (Real.exp (-t / 2) : ℂ) ^ 2 * conj (f t) * g t := by ring
    _ = _ := by rw [h]

theorem memLp_halfWeighted_of_exp_bound (f : ℝ → ℂ)
    (hc : Continuous f)
    (hf : f =O[atTop] (fun t : ℝ => Real.exp ((1 / 4) * t))) :
    MemLp (halfWeighted f) 2 (volume.restrict (Ioi 0)) := by
  have hs : (fun t : ℝ => ‖f t‖ ^ 2) =O[atTop]
      (fun t : ℝ => Real.exp ((1 / 2) * t)) := by
    convert hf.norm_left.pow 2 using 1
    funext t
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hcont : Continuous (fun t : ℝ => ‖f t‖ ^ 2) := hc.norm.pow 2
  have hi := integrableOn_exp_neg_smul_of_isBigO_exp (c := 0)
    (hcont.continuousOn.locallyIntegrableOn measurableSet_Ici) hs
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hi' : IntegrableOn (fun t : ℝ => Real.exp (-t) * ‖f t‖ ^ 2) (Ioi 0) := by
    simpa only [neg_mul, one_mul, smul_eq_mul] using hi.mono_set Ioi_subset_Ici_self
  have hw : Continuous (halfWeighted f) := by
    unfold halfWeighted
    have he : Continuous (fun t : ℝ => (Real.exp (-t / 2) : ℂ)) := by fun_prop
    exact he.mul hc
  apply (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable.restrict).mpr
  change Integrable (fun t => Real.exp (-t) * ‖f t‖ ^ 2)
    (volume.restrict (Ioi 0)) at hi'
  convert! hi' using 1
  funext t
  exact halfWeighted_norm_sq f t

theorem memLp_halfWeighted_laguerre (n : ℕ) :
    MemLp (halfWeighted (laguerreValue n)) 2 (volume.restrict (Ioi 0)) := by
  apply memLp_halfWeighted_of_exp_bound
  · exact continuous_iff_continuousAt.mpr fun t => (hasDerivAt_laguerreValue n t).continuousAt
  · exact polynomial_eval_isBigO_exp (laguerrePolynomial n) (1 / 4) (by norm_num)

noncomputable def laguerreL2 (n : ℕ) : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (memLp_halfWeighted_laguerre n).toLp (halfWeighted (laguerreValue n))

theorem inner_laguerreL2_halfWeighted (n : ℕ) (f : ℝ → ℂ)
    (hf : MemLp (halfWeighted f) 2 (volume.restrict (Ioi 0))) :
    inner ℂ (laguerreL2 n) (hf.toLp (halfWeighted f)) = laguerreCoefficientIntegral f n := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_halfWeighted_laguerre n).coeFn_toLp, hf.coeFn_toLp] with t hn ht
  rw [RCLike.inner_apply']
  change laguerreL2 n t = halfWeighted (laguerreValue n) t at hn
  rw [hn, ht, halfWeighted_inner]
  simp only [laguerreValue, conj_laguerrePolynomial_eval]
  change (Real.exp (-t) : ℂ) * (laguerrePolynomial n).eval (t : ℂ) * f t =
    (Real.exp (-t) : ℂ) * f t * (laguerrePolynomial n).eval (t : ℂ)
  ring

theorem orthonormal_laguerreL2 : Orthonormal ℂ laguerreL2 := by
  apply orthonormal_iff_ite.mpr
  intro n m
  change inner ℂ (laguerreL2 n)
    ((memLp_halfWeighted_laguerre m).toLp (halfWeighted (laguerreValue m))) = _
  rw [inner_laguerreL2_halfWeighted]
  change (∫ t in Ioi (0 : ℝ), (Real.exp (-t) : ℂ) *
    (laguerrePolynomial m).eval (t : ℂ) * (laguerrePolynomial n).eval (t : ℂ)) = _
  simpa only [conj_laguerrePolynomial_eval, eq_comm] using integral_laguerre_orthonormal m n

theorem laguerreCoefficientIntegral_tendsto_zero (f : ℝ → ℂ)
    (hf : MemLp (halfWeighted f) 2 (volume.restrict (Ioi 0))) :
    Tendsto (laguerreCoefficientIntegral f) atTop (𝓝 0) := by
  have hs := orthonormal_laguerreL2.inner_products_summable (hf.toLp (halfWeighted f))
  simp only [inner_laguerreL2_halfWeighted] at hs
  have hz := hs.tendsto_atTop_zero
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hz
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h

end DefocusingNLS

end OAI
