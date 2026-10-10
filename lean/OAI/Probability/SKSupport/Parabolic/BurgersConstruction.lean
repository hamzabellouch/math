import Mathlib
import OAI.Probability.SKSupport.Control.CoefficientApprox
import OAI.Probability.SKSupport.Parabolic.AffineEvolution

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma hasDerivAt_spatialJet {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n+1) f x) x := by
  simpa only [iteratedDeriv_succ] using
    ((contDiff_iteratedDeriv_infty hf n).differentiable (by simp) x).hasDerivAt

def burgersRate (r : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  (1/2:ℝ)*iteratedDeriv 2 (r t) x+r t x*deriv (r t) x

structure SmoothBurgers (r : ℝ → ℝ → ℝ) : Prop where
  family : BoundedSmoothFamily r
  continuous : ∀ T, ContinuousOn (fun p : ℝ × ℝ => r p.1 p.2) (Icc (0:ℝ) T ×ˢ univ)
  time_derivative : ∀ n t, 0 < t → ∀ x,
    HasDerivAt (fun s => iteratedDeriv n (r s) x) (iteratedDeriv n (burgersRate r t) x) t

def gaussianBurgers (c : ℝ) (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  c*deriv (varianceLogHeat c t f) x

lemma gaussianBurgers_jet {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c)
    (n : ℕ) (t x : ℝ) : iteratedDeriv n (gaussianBurgers c f t) x =
      c*iteratedDeriv (n+1) (varianceLogHeat c t f) x := by
  change iteratedDeriv n (fun x => c*deriv (varianceLogHeat c t f) x) x = _
  rw [iteratedDeriv_const_mul c
    ((regularDatum_varianceLogHeat hf hLip hc t).deriv_bounded.smooth.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt),iteratedDeriv_succ']

lemma gaussianBurgers_rate {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c)
    (t : ℝ) : burgersRate (gaussianBurgers c f) t = fun x => c*deriv (gaussianRate c f t) x := by
  have hG := (regularDatum_varianceLogHeat hf hLip hc t).smooth
  funext x
  have h₁ := hasDerivAt_spatialJet hG 1 x
  have h₂ := hasDerivAt_spatialJet hG 2 x
  have hd : HasDerivAt (gaussianRate c f t)
      ((1/2:ℝ)*iteratedDeriv 3 (varianceLogHeat c t f) x+
        c*deriv (varianceLogHeat c t f) x*iteratedDeriv 2 (varianceLogHeat c t f) x) x := by
    convert (h₂.const_mul (1/2:ℝ)).add ((h₁.pow 2).const_mul (c/2)) using 1 <;>
      first | rfl | ((try funext y); simp only [gaussianRate, Pi.add_apply, Pi.pow_apply,iteratedDeriv_succ,iteratedDeriv_zero] <;> ring)
  rw [hd.deriv,burgersRate,gaussianBurgers_jet hf hLip hc 2]
  have he := gaussianBurgers_jet hf hLip hc 1 t x
  simp only [iteratedDeriv_one] at he
  rw [he]
  dsimp only [gaussianBurgers]
  ring

theorem gaussianBurgers_smooth {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) :
    SmoothBurgers (gaussianBurgers c f) := by
  refine ⟨(varianceGradient_family hf hLip hc).const_mul c,?_,?_⟩
  · intro T
    exact continuousOn_const.mul (varianceGradient_continuousOn hf hLip hc T)
  · intro n t ht x
    have he : (fun s => iteratedDeriv n (gaussianBurgers c f s) x) =
        fun s => c*iteratedDeriv (n+1) (varianceLogHeat c s f) x :=
      funext (fun s => gaussianBurgers_jet hf hLip hc n s x)
    rw [he,gaussianBurgers_rate hf hLip hc,
      iteratedDeriv_const_mul c (((gaussianRate_family hf hLip hc).deriv.regular t).smooth.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt),← iteratedDeriv_succ']
    exact (hasDerivAt_varianceLogHeat_derivative hf hLip hc ht (n+1) x).const_mul c

lemma even_deriv_odd {f : ℝ → ℝ} (hf : Differentiable ℝ f) (he : Function.Even f) :
    Function.Odd (deriv f) := by
  intro x
  have hh := (hf (-x)).hasDerivAt.comp x ((hasDerivAt_id x).neg)
  have heq : (fun y => f (-y)) = f := funext he
  change HasDerivAt (fun y => f (-y)) (deriv f (-x)*(-1)) x at hh
  rw [heq] at hh
  linarith [hh.deriv]

lemma odd_deriv_even {f : ℝ → ℝ} (hf : Differentiable ℝ f) (he : Function.Odd f) :
    Function.Even (deriv f) := by
  intro x
  have hh := (hf (-x)).hasDerivAt.comp x ((hasDerivAt_id x).neg)
  have heq : (fun y => f (-y)) = fun y => -f y := funext he
  change HasDerivAt (fun y => f (-y)) (deriv f (-x)*(-1)) x at hh
  rw [heq] at hh
  have hder := (hf x).hasDerivAt.neg
  have he' := hh.unique hder
  linarith

lemma gaussianBurgers_odd {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (he : Function.Even f)
    {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : Function.Odd (gaussianBurgers c f t) := by
  have heq : varianceLogHeat c t f = logSemigroup c (Real.toNNReal t) f :=
    funext (varianceLogHeat_eq_logSemigroup_toNNReal hf.smooth.continuous.measurable c t)
  have hodd := even_deriv_odd ((regularDatum_varianceLogHeat hf hLip hc t).smooth.differentiable (by simp))
    (by rw [heq]; exact logSemigroup_even hf.smooth.continuous.measurable he _ _)
  intro x
  simp only [gaussianBurgers,hodd x,mul_neg]

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma inverse_forwardTime_family {a : ℝ} (ha : 0 < a) :
    BoundedSmoothFamily (fun t (_x : ℝ) => (forwardTime a t)⁻¹) := by
  apply BoundedSmoothFamily.timeConst (C := Real.toNNReal a⁻¹)
    (continuous_forwardTime a).measurable.inv
  intro t
  change |(forwardTime a t)⁻¹| ≤ (Real.toNNReal a⁻¹ : ℝ)
  rw [Real.coe_toNNReal _ (inv_nonneg.mpr ha.le),abs_of_pos (inv_pos.mpr (forwardTime_pos ha t))]
  exact inv_anti₀ ha (le_add_of_nonneg_right (le_max_right _ _))

lemma inverse_forwardTime_continuous {a : ℝ} (ha : 0 < a) :
    Continuous (fun t => (forwardTime a t)⁻¹) :=
  (continuous_forwardTime a).inv₀ (fun t => ne_of_gt (forwardTime_pos ha t))

lemma forwardCorrectionRate_affine {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) :
    AffineSmoothFamily (forwardCorrectionRate a f) := by
  have hU := forwardGradient_family ha hf hLip
  have hUc := forwardGradient_continuous ha hf hLip
  have hUx : Continuous (fun p : ℝ × ℝ => deriv (deriv (forwardCorrection a f p.1)) p.2) := by
    simpa only [iteratedDeriv_one] using hU.continuous_iteratedDeriv hUc 1
  have hI := inverse_forwardTime_family ha
  have hIc : Continuous (fun p : ℝ × ℝ => (forwardTime a p.1)⁻¹) :=
    (inverse_forwardTime_continuous ha).comp continuous_fst
  let A (t x : ℝ) := (1/2:ℝ)*deriv (deriv (forwardCorrection a f t)) x+
    (1/2:ℝ)*(deriv (forwardCorrection a f t) x)^2-(1/2:ℝ)*(forwardTime a t)⁻¹
  let B (t x : ℝ) := -(forwardTime a t)⁻¹*deriv (forwardCorrection a f t) x
  refine ⟨A,B,?_,?_,?_,?_,?_⟩
  · convert ((hU.deriv.const_mul (1/2:ℝ)).add ((hU.mul hU).const_mul (1/2:ℝ))).add
      (hI.const_mul (-1/2:ℝ)) using 1
    funext t x
    dsimp [A]
    ring
  · dsimp [A]
    exact ((hUx.const_mul (1/2:ℝ)).add ((hUc.pow 2).const_mul (1/2:ℝ))).sub (hIc.const_mul (1/2:ℝ))
  · convert (hI.const_mul (-1)).mul hU using 1
    simp only [neg_one_mul]
    rfl
  · exact hIc.neg.mul hUc
  · funext t x
    dsimp [A,B,forwardCorrectionRate]
    simp only [iteratedDeriv_succ,iteratedDeriv_zero,div_eq_mul_inv]
    ring

lemma hasDerivAt_forwardCorrection_jet {a t : ℝ} (ha : 0 < a) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (ht : 0 < t) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun s => iteratedDeriv n (forwardCorrection a f s) x)
      (iteratedDeriv n (forwardCorrectionRate a f t) x) t :=
  hasDerivAt_affine_evolution_jet (forwardCorrection_continuous ha hf hLip)
    (forwardCorrectionRate_affine ha hf hLip) (forwardCorrection_smooth hf hLip)
    (fun _ htt x => hasDerivAt_forwardCorrection ha hf hLip htt x) ht n x

lemma forwardScore_affine {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) : AffineSmoothFamily (forwardScore a f) := by
  have hI := inverse_forwardTime_family ha
  have hIc : Continuous (fun p : ℝ × ℝ => (forwardTime a p.1)⁻¹) :=
    (inverse_forwardTime_continuous ha).comp continuous_fst
  have hU := forwardGradient_family ha hf hLip
  have hUc := forwardGradient_continuous ha hf hLip
  convert (hI.affine_id_mul hIc).add ((hU.affine hUc).const_mul (-1)) using 1
  funext t x
  simp only [forwardScore,div_eq_mul_inv,neg_one_mul,sub_eq_add_neg]

lemma forwardScore_deriv {a : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (t x : ℝ) :
    deriv (forwardScore a f t) x=(forwardTime a t)⁻¹-iteratedDeriv 2 (forwardCorrection a f t) x := by
  have hh := ((hasDerivAt_id x).div_const (forwardTime a t)).sub
    (hasDerivAt_spatialJet (forwardCorrection_smooth (a := a) hf hLip t) 1 x)
  convert hh.deriv using 1 <;> first | rfl | (simp only [one_div,iteratedDeriv_one] <;> rfl)

lemma forwardScore_deriv_family {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) :
    BoundedSmoothFamily (fun t => deriv (forwardScore a f t)) := by
  convert (inverse_forwardTime_family ha).add ((forwardGradient_family ha hf hLip).deriv.const_mul (-1)) using 1
  funext t x
  rw [forwardScore_deriv hf hLip]
  simp only [iteratedDeriv_succ,iteratedDeriv_zero,neg_one_mul,sub_eq_add_neg]

lemma forwardScore_second {a : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (t x : ℝ) :
    iteratedDeriv 2 (forwardScore a f t) x = -iteratedDeriv 3 (forwardCorrection a f t) x := by
  have he : deriv (forwardScore a f t) = fun x =>
      (forwardTime a t)⁻¹-iteratedDeriv 2 (forwardCorrection a f t) x := funext (forwardScore_deriv hf hLip t)
  rw [iteratedDeriv_succ (n := 1),iteratedDeriv_one,he]
  exact ((hasDerivAt_spatialJet (forwardCorrection_smooth (a := a) hf hLip t) 2 x).const_sub _).deriv

def scoreRate (s : ℝ → ℝ → ℝ) (t x : ℝ) :=
  (1/2:ℝ)*iteratedDeriv 2 (s t) x-s t x*deriv (s t) x

lemma forwardCorrectionRate_deriv {a : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (t x : ℝ) :
    deriv (forwardCorrectionRate a f t) x =
      (1/2:ℝ)*iteratedDeriv 3 (forwardCorrection a f t) x+
      deriv (forwardCorrection a f t) x*iteratedDeriv 2 (forwardCorrection a f t) x-
      ((forwardTime a t)⁻¹*deriv (forwardCorrection a f t) x+
        x/forwardTime a t*iteratedDeriv 2 (forwardCorrection a f t) x) := by
  have hL := forwardCorrection_smooth (a := a) hf hLip t
  have hh := ((((hasDerivAt_spatialJet hL 2 x).const_mul (1/2:ℝ)).add
    (((hasDerivAt_spatialJet hL 1 x).pow 2).const_mul (1/2:ℝ))).sub
    (((hasDerivAt_id x).div_const (forwardTime a t)).mul (hasDerivAt_spatialJet hL 1 x))).sub_const
    ((1/2:ℝ)/forwardTime a t)
  have hh' : HasDerivAt (forwardCorrectionRate a f t)
      ((1/2:ℝ)*iteratedDeriv 3 (forwardCorrection a f t) x+
      deriv (forwardCorrection a f t) x*iteratedDeriv 2 (forwardCorrection a f t) x-
      ((forwardTime a t)⁻¹*deriv (forwardCorrection a f t) x+
        x/forwardTime a t*iteratedDeriv 2 (forwardCorrection a f t) x)) x := by
    convert hh using 1 <;> first | rfl | ((try funext y); simp only [forwardCorrectionRate,iteratedDeriv_one,id_eq,one_div,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply] <;> ring)
  exact hh'.deriv

lemma hasDerivAt_forwardScore {a t : ℝ} (ha : 0 < a) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun u => forwardScore a f u x) (scoreRate (forwardScore a f) t x) t := by
  have hd := ((hasDerivAt_const t x).div (hasDerivAt_forwardTime ht)
    (ne_of_gt (forwardTime_pos ha t))).sub (hasDerivAt_forwardCorrection_jet ha hf hLip ht 1 x)
  convert hd using 1
  · funext u
    simp only [forwardScore,iteratedDeriv_one,Pi.sub_apply,Pi.div_apply]
  simp only [iteratedDeriv_one]
  rw [forwardCorrectionRate_deriv hf hLip, scoreRate,forwardScore_second hf hLip,forwardScore_deriv hf hLip]
  dsimp only [forwardScore]
  field_simp [ne_of_gt (forwardTime_pos ha t)]
  ring

end ZeroTemperatureSK.Heat

end
end

end OAI
