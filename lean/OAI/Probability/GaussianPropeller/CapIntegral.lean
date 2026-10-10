import OAI.Probability.GaussianPropeller.Polar

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar
open scoped Topology

lemma p_eq_integral_indicator (a : ℝ) :
    p a = ∫ x : ℝ, (Ioi a).indicator (fun _ => (1:ℝ)) x ∂gaussianReal 0 1 := by
  rw [integral_gaussianReal_std]
  have he : (fun x : ℝ => (Ioi a).indicator (fun _ => (1:ℝ)) x*density x) =
      (Ioi a).indicator density := by
    funext x
    by_cases hx : x∈Ioi a <;> simp [hx]
  rw [he,integral_indicator measurableSet_Ioi]
  rfl

lemma p_le_one (a : ℝ) : p a ≤ 1 := by
  rw [p_eq_integral_indicator, integral_indicator measurableSet_Ioi, setIntegral_const,
    smul_eq_mul, mul_one]
  exact measureReal_le_one

lemma density_le_one (a : ℝ) : density a ≤ 1 := by
  unfold density
  rw [Real.exp_le_one_iff]
  linarith [sq_nonneg a]

variable {n : ℕ}
abbrev CE (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def capP (n : ℕ) (a : ℝ) : ℝ := ∫ y : CE n, p (a*‖y‖) ∂stdGaussian (CE n)
noncomputable def capM (n : ℕ) (a : ℝ) : ℝ := gaussianConst * ∫ y : CE n, density (a*‖y‖) ∂stdGaussian (CE n)

lemma integrable_p_norm (a : ℝ) : Integrable (fun y : CE n => p (a*‖y‖)) (stdGaussian (CE n)) := by
  apply Integrable.mono' (integrable_const (1:ℝ))
    (((continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_p x).continuousAt)).comp (by fun_prop)).aestronglyMeasurable)
  filter_upwards [] with y
  dsimp only [Function.comp_def]
  rw [Real.norm_eq_abs,abs_of_pos (p_pos _)]
  exact p_le_one _

lemma capP_zero (n : ℕ) : capP n 0 = 1/2 := by
  simp [capP,p,tail_zero]

lemma hasDerivAt_capP (a : ℝ) : HasDerivAt (capP n)
    (-gaussianConst * ∫ y : CE n, ‖y‖*density (a*‖y‖) ∂stdGaussian (CE n)) a := by
  have hc : 0 < gaussianConst := by dsimp [gaussianConst]; positivity
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=univ)
    (bound:= fun y : CE n => gaussianConst*‖y‖)
    (F:= fun s y => p (s*‖y‖))
    (F':=fun s y => -gaussianConst*(‖y‖*density (s*‖y‖)))
    (by simp : univ ∈ 𝓝 a)
    (Filter.Eventually.of_forall (fun s => (integrable_p_norm s).aestronglyMeasurable))
    (integrable_p_norm a)
    (by unfold density; fun_prop : AEStronglyMeasurable (fun y : CE n => -gaussianConst*(‖y‖*density (a*‖y‖))) (stdGaussian (CE n)))
    (by
      filter_upwards [] with y
      intro s _
      simp only [norm_mul,norm_neg,Real.norm_eq_abs,abs_of_pos hc,abs_of_nonneg (norm_nonneg y),abs_of_pos (show 0 < density (s*‖y‖) from Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (by nlinarith only [density_le_one (s*‖y‖),norm_nonneg y] :
        ‖y‖*density (s*‖y‖) ≤ ‖y‖) hc.le)
    (IsGaussian.integrable_id.norm.const_mul gaussianConst)
    (by
      filter_upwards [] with y
      intro s _
      convert (hasDerivAt_p (s*‖y‖)).comp s ((hasDerivAt_id s).mul_const ‖y‖) using 1 <;> first | rfl | ring)
  have hd2 := hd.2
  rw [integral_const_mul] at hd2
  exact hd2

lemma capM_eq (hn : 0<n) (a : ℝ) :
    capM n a = gaussianConst * (Real.sqrt (1+a^2))⁻¹^n := by
  let : NeZero n := ⟨by omega⟩
  have hh := integral_norm_pow_exp (ι:=Fin n) 0 (a:=a^2/2) (by positivity)
  have hs := radial_scale (n-1) (b:=a^2/2+1/2) (by positivity)
  simp only [Fintype.card_fin, add_zero, pow_zero, one_mul] at hh
  unfold capM
  have he : (fun y : CE n => density (a*‖y‖)) = fun y => Real.exp (-(a^2/2)*‖y‖^2) := by
    funext y; unfold density; congr 1; ring
  rw [he,hh,hs,show 2*(a^2/2+1/2)=1+a^2 by ring,
    show n-1+1=n by omega, mul_div_cancel_right₀ _ (radial_pos _ (by norm_num)).ne']

lemma capP_deriv_two (a : ℝ) : HasDerivAt (capP 2)
    (-(1/2:ℝ)*(Real.sqrt (1+a^2))⁻¹^3) a := by
  have hh := integral_norm_pow_exp (ι:=Fin 2) 1 (a:=a^2/2) (by positivity)
  have hs := radial_scale 2 (b:=a^2/2+1/2) (by positivity)
  norm_num only [Fintype.card_fin, Nat.reduceSub, Nat.reduceAdd, pow_one, radial_half_one] at hh
  have hd := hasDerivAt_capP (n:=2) a
  have he : (fun y : CE 2 => ‖y‖*density (a*‖y‖)) = fun y => ‖y‖*Real.exp (-(a^2/2)*‖y‖^2) := by
    funext y; unfold density; congr 2; ring
  rw [he,hh,div_one,hs,show 2*(a^2/2+1/2)=1+a^2 by ring,radial_half_two] at hd
  convert hd using 1
  dsimp [gaussianConst]
  field_simp

lemma capP_two (a : ℝ) : capP 2 a = (1-a/Real.sqrt (1+a^2))/2 := by
  have hp (x : ℝ) : 0 < 1+x^2 := by positivity
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => (1-x/Real.sqrt (1+x^2))/2)
      (-(1/2:ℝ)*(Real.sqrt (1+x^2))⁻¹^3) x := by
    convert ((hasDerivAt_const x 1).sub ((hasDerivAt_id x).div
      (((hasDerivAt_pow 2 x).const_add 1).sqrt (hp x).ne') (Real.sqrt_pos.mpr (hp x)).ne')).div_const 2 using 1 <;> first | rfl | (dsimp; field_simp; nlinarith only [Real.sq_sqrt (hp x).le])
  have he := is_const_of_deriv_eq_zero (fun x => ((hasDerivAt_capP (n:=2) x).sub (hd x)).differentiableAt)
  have he' : ∀ x, deriv (fun x => capP 2 x-(1-x/Real.sqrt (1+x^2))/2) x=0 := by
    intro x
    have hx := ((capP_deriv_two x).fun_sub (hd x)).deriv
    rw [sub_self] at hx
    exact hx
  have hg := he he' a 0
  simp only [Pi.sub_apply, capP_zero,zero_div,sub_zero,one_div] at hg
  linarith

end GaussianPropeller.Cap

end OAI
