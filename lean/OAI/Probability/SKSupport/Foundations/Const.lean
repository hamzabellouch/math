import Mathlib
import OAI.Probability.SKSupport.Parabolic.TiltedMean

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma RegularDatum.const (a : ℝ) : RegularDatum (fun _ : ℝ => a) := by
  refine ⟨contDiff_const, ?_⟩
  simpa only [deriv_const'] using BoundedSmooth.const 0

lemma boundedSmooth_semigroup {g : ℝ → ℝ} (hg : BoundedSmooth g) (h : ℝ≥0) :
    BoundedSmooth (semigroup h g) := by
  have hm := boundedSmooth_tiltedMean (RegularDatum.const 0)
    (LipschitzWith.const (0:ℝ)) hg (c := 0) le_rfl h
  have he : tiltedMean 0 h (fun _ => 0) g = semigroup h g := by
    funext x; simp [tiltedMean, semigroup]
  rw [he] at hm
  exact hm

lemma regularDatum_semigroup {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (h : ℝ≥0) :
    RegularDatum (semigroup h f) := by
  have he : deriv (semigroup h f) = semigroup h (deriv f) := funext (fun x =>
    (hasDerivAt_semigroup (hf.smooth.of_le (by simp)) hLip h x).deriv)
  have hd := boundedSmooth_semigroup hf.deriv_bounded h
  constructor
  · apply contDiff_infty_iff_deriv.mpr
    constructor
    · exact fun x => (hasDerivAt_semigroup (hf.smooth.of_le (by simp)) hLip h x).differentiableAt
    · rw [he]; exact hd.smooth
  · rw [he]; exact hd

lemma regularDatum_logSemigroup {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c)
    (h : ℝ≥0) : RegularDatum (logSemigroup c h f) := by
  by_cases hc0 : c = 0
  · subst c
    have he : logSemigroup 0 h f = semigroup h f := by funext x; simp [logSemigroup]
    rw [he]; exact regularDatum_semigroup hf hLip h
  have hder : deriv (logSemigroup c h f) = tiltedMean c h f (deriv f) := by
    funext x
    exact (hasDerivAt_logSemigroup (hf.smooth.of_le (by simp)) hLip (lt_of_le_of_ne hc (Ne.symm hc0)) h x).deriv
  have hd := boundedSmooth_tiltedMean hf hLip hf.deriv_bounded hc h
  constructor
  · apply contDiff_infty_iff_deriv.mpr
    constructor
    · intro x
      exact (hasDerivAt_logSemigroup (hf.smooth.of_le (by simp)) hLip (lt_of_le_of_ne hc (Ne.symm hc0)) h x).differentiableAt
    · rw [hder]; exact hd.smooth
  · rw [hder]; exact hd

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat

lemma integrable_mul_standardGaussianPDF {g : ℝ → ℝ}
    (hg : Integrable g (gaussianReal 0 1)) :
    Integrable (fun y => gaussianPDFReal 0 1 y*g y) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero] at hg
  have hh := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1) (Filter.Eventually.of_forall
      (fun y => (gaussianPDF_lt_top (μ := 0) (v := 1) (x := y))))).mp hg
  simpa only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),
    smul_eq_mul] using hh

lemma hasDerivAt_standardGaussianPDF (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x*gaussianPDFReal 0 1 x) x := by
  have he : gaussianPDFReal 0 1 = fun y : ℝ =>
      (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-y^2/2) := by
    funext y
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [he]
  have hd := (((((hasDerivAt_id x).pow 2).neg.div_const (2:ℝ)).exp).const_mul
    ((Real.sqrt (2*Real.pi))⁻¹))
  apply hd.congr_deriv
  simp only [id_eq, Pi.pow_apply, Pi.neg_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

lemma standardGaussian_stein {g g' : ℝ → ℝ} (hd : ∀ x, HasDerivAt g (g' x) x)
    (hg : Integrable g (gaussianReal 0 1)) (hg' : Integrable g' (gaussianReal 0 1))
    (hyg : Integrable (fun y => y*g y) (gaussianReal 0 1)) :
    (∫ y, y*g y ∂gaussianReal 0 1) = ∫ y, g' y ∂gaussianReal 0 1 := by
  have hv := integrable_mul_standardGaussianPDF hg
  have hv' := integrable_mul_standardGaussianPDF hg'
  have hyv := integrable_mul_standardGaussianPDF hyg
  have ha : Integrable (fun y => g y*(-y*gaussianPDFReal 0 1 y)) := by
    convert hyv.neg using 1
    funext y; simp only [Pi.neg_apply]; ring
  have hb : Integrable (fun y => g' y*gaussianPDFReal 0 1 y) := by
    simpa only [mul_comm] using hv'
  have hc : Integrable (fun y => g y*gaussianPDFReal 0 1 y) := by
    simpa only [mul_comm] using hv
  have hi := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := g) (u' := g') (v := gaussianPDFReal 0 1)
    (v' := fun y => -y*gaussianPDFReal 0 1 y)
    (fun y _ => hd y) (fun y _ => hasDerivAt_standardGaussianPDF y) ha hb hc
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  have he : (fun y => g y*(-y*gaussianPDFReal 0 1 y)) =
      fun y => -(gaussianPDFReal 0 1 y*(y*g y)) := by funext y; ring
  rw [he, integral_neg] at hi
  have hh := neg_injective hi
  simpa only [mul_comm] using hh

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat

def ExponentialBound (g : ℝ → ℝ) : Prop :=
  ∃ A K : ℝ≥0, ∀ z, |g z| ≤ (A:ℝ)*Real.exp ((K:ℝ)*|z|)

lemma ExponentialBound.of_bounded {g : ℝ → ℝ} {A : ℝ≥0} (hA : ∀ z, |g z| ≤ A) :
    ExponentialBound g := by
  exact ⟨A, 0, fun z => by simpa using hA z⟩

lemma integrable_abs_mul_exp_abs (K : ℝ) :
    Integrable (fun y : ℝ => |y| *Real.exp (K*|y|)) (gaussianReal 0 1) := by
  apply Integrable.mono' (integrable_exp_abs (K+1) 0 1) (by fun_prop)
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    |y| *Real.exp (K*|y|) ≤ Real.exp |y| *Real.exp (K*|y|) := by
      gcongr
      linarith [Real.add_one_le_exp |y|]
    _ = Real.exp ((K+1)*|y|) := by rw [← Real.exp_add]; congr 1; ring

lemma exponentialBound_scaled {g : ℝ → ℝ} {A K : ℝ≥0}
    (hg : ∀ z, |g z| ≤ (A:ℝ)*Real.exp ((K:ℝ)*|z|))
    (x a y R : ℝ) (ha : |a| ≤ R) :
    |g (x+a*y)| ≤ (A:ℝ)*Real.exp ((K:ℝ)*|x|)*Real.exp (((K:ℝ)*R)*|y|) := by
  calc
    _ ≤ (A:ℝ)*Real.exp ((K:ℝ)*|x+a*y|) := hg _
    _ ≤ (A:ℝ)*Real.exp ((K:ℝ)*(|x|+R*|y|)) := by
      gcongr
      exact (abs_add_le _ _).trans (by rw [abs_mul]; gcongr)
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

lemma integrable_scaled_of_expBound {g : ℝ → ℝ} (hgm : Measurable g)
    (hg : ExponentialBound g) (a x : ℝ) :
    Integrable (fun y => g (x+a*y)) (gaussianReal 0 1) := by
  obtain ⟨A,K,hg⟩ := hg
  apply Integrable.mono' ((integrable_exp_abs ((K:ℝ)*|a|) 0 1).const_mul
    ((A:ℝ)*Real.exp ((K:ℝ)*|x|)))
    ((hgm.comp (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable)
  filter_upwards [] with y
  change ‖g (x+a*y)‖ ≤ _
  simpa only [Real.norm_eq_abs] using exponentialBound_scaled hg x a y |a| le_rfl

lemma integrable_mul_scaled_of_expBound {g : ℝ → ℝ} (hgm : Measurable g)
    (hg : ExponentialBound g) (a x : ℝ) :
    Integrable (fun y => y*g (x+a*y)) (gaussianReal 0 1) := by
  obtain ⟨A,K,hg⟩ := hg
  apply Integrable.mono' ((integrable_abs_mul_exp_abs ((K:ℝ)*|a|)).const_mul
    ((A:ℝ)*Real.exp ((K:ℝ)*|x|)))
    ((measurable_id.mul (hgm.comp (measurable_const.add (measurable_const.mul measurable_id)))).aestronglyMeasurable)
  filter_upwards [] with y
  change ‖y*g (x+a*y)‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ |y| *((A:ℝ)*Real.exp ((K:ℝ)*|x|)*Real.exp (((K:ℝ)*|a|)*|y|)) := by
      gcongr
      exact exponentialBound_scaled hg x a y |a| le_rfl
    _ = _ := by ring

def scaled (a : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, g (x+a*y) ∂gaussianReal 0 1

lemma semigroup_eq_scaled {g : ℝ → ℝ} (hgm : Measurable g) (h : ℝ≥0) (x : ℝ) :
    semigroup h g x = scaled (Real.sqrt (h:ℝ)) g x := by
  have hs : (gaussianReal 0 1).map (fun y : ℝ => Real.sqrt (h:ℝ)*y) = gaussianReal 0 h := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext; simp [Real.sq_sqrt h.coe_nonneg]
  unfold semigroup scaled
  rw [← hs]
  exact integral_map (by fun_prop)
    (show AEStronglyMeasurable (fun y => g (x+y)) _ from
      (hgm.comp (measurable_const.add measurable_id)).aestronglyMeasurable)

lemma continuous_scaled {g : ℝ → ℝ} (hgc : Continuous g) (hg : ExponentialBound g)
    (x : ℝ) : Continuous (fun a => scaled a g x) := by
  obtain ⟨A,K,hg⟩ := hg
  apply continuous_iff_continuousAt.mpr
  intro a
  apply continuousAt_of_dominated
    (bound := fun y => (A:ℝ)*Real.exp ((K:ℝ)*|x|)*Real.exp (((K:ℝ)*(|a|+1))*|y|))
  · exact Filter.Eventually.of_forall (fun z => (by fun_prop))
  · filter_upwards [Metric.ball_mem_nhds a (show (0:ℝ)<1 by norm_num)] with z hz
    filter_upwards [] with y
    have hz' : |z| ≤ |a|+1 := by
      have ht := abs_add_le (z-a) a
      rw [sub_add_cancel] at ht
      have hd : |z-a| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hz
      linarith
    simpa only [Real.norm_eq_abs] using exponentialBound_scaled hg x z y (|a|+1) hz'
  · exact (integrable_exp_abs ((K:ℝ)*(|a|+1)) 0 1).const_mul _
  · filter_upwards [] with y
    exact hgc.continuousAt.comp (by fun_prop)

lemma hasDerivAt_scaled {g : ℝ → ℝ} (hgc : ContDiff ℝ 1 g)
    (hg : ExponentialBound g) (hg' : ExponentialBound (deriv g)) (a x : ℝ) :
    HasDerivAt (fun z => scaled z g x)
      (∫ y, y*deriv g (x+a*y) ∂gaussianReal 0 1) a := by
  obtain ⟨A,K,hg'⟩ := hg'
  have hdm := hgc.continuous_deriv_one.measurable
  have hm : ∀ᶠ z in 𝓝 a, AEStronglyMeasurable (fun y => g (x+z*y)) (gaussianReal 0 1) :=
    Filter.Eventually.of_forall (fun z => by fun_prop)
  have hdmeas : AEStronglyMeasurable (fun y => y*deriv g (x+a*y)) (gaussianReal 0 1) := by fun_prop
  have hb : ∀ᵐ y ∂gaussianReal 0 1, ∀ z ∈ Metric.ball a 1,
      ‖y*deriv g (x+z*y)‖ ≤
        ((A:ℝ)*Real.exp ((K:ℝ)*|x|))*(|y| *Real.exp (((K:ℝ)*(|a|+1))*|y|)) := by
    filter_upwards [] with y z hz
    have hz' : |z| ≤ |a|+1 := by
      have ht := abs_add_le (z-a) a
      rw [sub_add_cancel] at ht
      have hd : |z-a| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hz
      linarith
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ |y| *((A:ℝ)*Real.exp ((K:ℝ)*|x|)*Real.exp (((K:ℝ)*(|a|+1))*|y|)) := by
        gcongr
        exact exponentialBound_scaled hg' x z y (|a|+1) hz'
      _ = _ := by ring
  have hD : ∀ᵐ y ∂gaussianReal 0 1, ∀ z ∈ Metric.ball a 1,
      HasDerivAt (fun w => g (x+w*y)) (y*deriv g (x+z*y)) z := by
    filter_upwards [] with y z hz
    convert (hgc.differentiable (by norm_num) (x+z*y)).hasDerivAt.comp z
      (((hasDerivAt_id z).mul_const y).const_add x) using 1 <;> first | rfl | simp [mul_comm]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds a (show (0:ℝ)<1 by norm_num)) hm
    (integrable_scaled_of_expBound hgc.continuous.measurable hg a x) hdmeas hb
    ((integrable_abs_mul_exp_abs ((K:ℝ)*(|a|+1))).const_mul _) hD).2

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
