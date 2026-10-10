import OAI.NumberTheory.TwoPointCorrelations.MRTPrimeMoments
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

/-! Sampling a differentiable function at separated points.  Unit
intervals give a finite Sobolev estimate, which will be applied to the
prime-polynomial powers already expanded into Dirichlet coefficients. -/

namespace TwoPointCorrelations

open Finset MeasureTheory Set
open scoped RealInnerProductSpace

lemma mrt_value_le_unit_integral (F F' B : ℝ → ℝ)
    (hF : Continuous F) (hF' : ∀ t, HasDerivAt F (F' t) t)
    (hB : Continuous B) (hB0 : ∀ t, 0 ≤ B t)
    (hd : ∀ t, |F' t| ≤ B t) (a : ℝ) :
    F a ≤ ∫ t in a..(a + 1), F t + B t := by
  have hiB : IntervalIntegrable B volume a (a + 1) := hB.intervalIntegrable a (a + 1)
  have hp (y : ℝ) (hy : y ∈ Icc a (a + 1)) :
      F a ≤ F y + ∫ t in a..(a + 1), B t := by
    have hdiff : ‖F y - F a‖ ≤ ∫ t in a..y, B t := by
      apply norm_sub_le_integral_of_norm_deriv_le_of_le hy.1 hF.continuousOn
        (fun t _ => (hF' t).differentiableAt.differentiableWithinAt)
      · exact Filter.Eventually.of_forall fun t _ => by
          rw [(hF' t).deriv, Real.norm_eq_abs]
          exact hd t
      · exact hB.intervalIntegrable a y
    have hm : (∫ t in a..y, B t) ≤ ∫ t in a..(a + 1), B t :=
      intervalIntegral.integral_mono_interval le_rfl hy.1 hy.2
        (Filter.Eventually.of_forall hB0) hiB
    have he : F a - F y ≤ ‖F y - F a‖ := by
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact le_abs_self _
    linarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by linarith : a ≤ a + 1)
    (continuous_const.intervalIntegrable a (a + 1))
    ((hF.add continuous_const).intervalIntegrable a (a + 1)) hp
  change (∫ t in a..(a + 1), F a) ≤
    ∫ t in a..(a + 1), F t + (∫ u in a..(a + 1), B u) at hi
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add
    (hF.intervalIntegrable a (a + 1))
    (continuous_const.intervalIntegrable a (a + 1)), intervalIntegral.integral_const] at hi
  have hlen : a + 1 - a = 1 := by ring
  simp only [hlen, one_smul] at hi
  rw [intervalIntegral.integral_add (hF.intervalIntegrable a (a + 1)) hiB]
  exact hi

lemma mrt_unit_intervals_disjoint (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) :
    Set.Pairwise (S : Set ℝ) (fun x y => Disjoint (Set.Ioc x (x + 1))
      (Set.Ioc y (y + 1))) := by
  intro x hx y hy hne
  have h := hsep x hx y hy hne
  by_cases hxy : x ≤ y
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy)] at h
    exact Ioc_disjoint_Ioc_of_le (by linarith)
  · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hxy))] at h
    exact (Ioc_disjoint_Ioc_of_le (by linarith : y + 1 ≤ x)).symm

lemma mrt_sum_unit_integrals_le (S : Finset ℝ) (G : ℝ → ℝ)
    (hG : Continuous G) (hG0 : ∀ t, 0 ≤ G t)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|)
    (a b : ℝ) (hab : a ≤ b)
    (hS : ∀ x ∈ S, a ≤ x ∧ x + 1 ≤ b) :
    (∑ x ∈ S, ∫ t in x..(x + 1), G t) ≤ ∫ t in a..b, G t := by
  have hint (x : ℝ) : (∫ t in x..(x + 1), G t) = ∫ t in Ioc x (x + 1), G t :=
    intervalIntegral.integral_of_le (by linarith)
  simp_rw [hint]
  rw [← integral_biUnion_finset S (fun _ _ => measurableSet_Ioc)
    (mrt_unit_intervals_disjoint S hsep)
    (fun x _ => (hG.intervalIntegrable x (x + 1)).1),
    intervalIntegral.integral_of_le hab]
  apply setIntegral_mono_set (hG.intervalIntegrable a b).1
    (Filter.Eventually.of_forall hG0)
  exact Filter.Eventually.of_forall fun t ht => by
    obtain ⟨x, hx, ht⟩ := mem_iUnion₂.mp ht
    exact ⟨lt_of_le_of_lt (hS x hx).1 ht.1, ht.2.trans (hS x hx).2⟩

/-- A finite separated sample is controlled by the ordinary square
integrals of a function and its derivative. -/
theorem mrt_separated_square_samples (S : Finset ℝ) (q q' : ℝ → ℂ)
    (hq : Continuous q) (hq' : Continuous q')
    (hd : ∀ t, HasDerivAt q (q' t) t)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|)
    (a b : ℝ) (hab : a ≤ b) (hS : ∀ x ∈ S, a ≤ x ∧ x + 1 ≤ b) :
    (∑ x ∈ S, ‖q x‖ ^ 2) ≤ ∫ t in a..b, 2 * ‖q t‖ ^ 2 + ‖q' t‖ ^ 2 := by
  let F := fun t => ‖q t‖ ^ 2
  let B := fun t => ‖q t‖ ^ 2 + ‖q' t‖ ^ 2
  have hB : Continuous B := (hq.norm.pow 2).add (hq'.norm.pow 2)
  have hder (t : ℝ) : |2 * inner ℝ (q t) (q' t)| ≤ B t := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hi := abs_real_inner_le_norm (q t) (q' t)
    dsimp only [B]
    nlinarith [sq_nonneg (‖q t‖ - ‖q' t‖)]
  calc
    _ ≤ ∑ x ∈ S, ∫ t in x..(x + 1), F t + B t := by
      apply sum_le_sum
      intro x _
      exact mrt_value_le_unit_integral F (fun t => 2 * inner ℝ (q t) (q' t)) B
        (hq.norm.pow 2) (fun t => (hd t).norm_sq) hB
        (fun t => by dsimp only [B]; positivity) hder x
    _ ≤ ∫ t in a..b, F t + B t :=
      mrt_sum_unit_integrals_le S (fun t => F t + B t) ((hq.norm.pow 2).add hB)
        (fun t => by dsimp only [F, B]; positivity)
        hsep a b hab hS
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only [F, B]
      ring

lemma mrt_exponential_polynomial_deriv {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) (t : ℝ) :
    HasDerivAt (mrtExponentialPolynomial S a freq)
      (mrtExponentialPolynomial S (fun i => a i * ((freq i : ℂ) * Complex.I)) freq t) t := by
  unfold mrtExponentialPolynomial
  apply HasDerivAt.fun_sum
  intro i _
  have h := (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (freq i : ℂ)).mul_const
    Complex.I).cexp.const_mul (a i)
  convert h using 1
  · funext y
    simp only [Complex.ofReal_mul, Complex.ofRealCLM_apply]
  · simp only [Complex.ofReal_mul, Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one]
    ring

end TwoPointCorrelations

end OAI
