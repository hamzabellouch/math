import Mathlib
import OAI.Probability.LogConcave.Analysis.PoincareVectorVariance
import OAI.Probability.LogConcave.JetEstimates.ArrayMatrix

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory Set
open scoped NNReal ENNReal

namespace TimeJet
variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def jet (f : ℝ × X → E) : ℕ → ℝ × X → E
  | 0 => f
  | n+1 => fun p => fderiv ℝ (jet f n) p (1,0)

lemma smooth {f : ℝ × X → E} (hf : ContDiff ℝ (⊤:ℕ∞) f) (n : ℕ) :
    ContDiff ℝ (⊤:ℕ∞) (jet f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

lemma hasDerivAt (f : ℝ × X → E) (hf : ContDiff ℝ (⊤:ℕ∞) f)
    (n : ℕ) (t : ℝ) (y : X) :
    HasDerivAt (fun s => jet f n (s,y)) (jet f (n+1) (t,y)) t := by
  exact (((smooth hf n).differentiable (by simp)) (t,y)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))

lemma eq_iteratedDeriv (f : ℝ × X → E) (hf : ContDiff ℝ (⊤:ℕ∞) f)
    (n : ℕ) (t : ℝ) (y : X) :
    jet f n (t,y)=iteratedDeriv n (fun s => f (s,y)) t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,←funext (fun t => ih t)]
    exact (hasDerivAt f hf n t y).deriv.symm
end TimeJet

namespace RMSIntegral
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] {μ : Measure Ω}

lemma integral_norm_sq_eq_eLpNorm (f : Ω → E) (hf : MemLp f 2 μ) :
    (∫x,‖f x‖^2 ∂μ)=(eLpNorm f 2 μ).toReal^2 := by
  have hh := MemLp.eLpNorm_eq_integral_rpow_norm (f:=f) (by norm_num : (2:ℝ≥0∞)≠0)
    (by norm_num : (2:ℝ≥0∞)≠⊤) hf
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hh
  rw [show (2:ℝ)⁻¹=1/2 by norm_num,←Real.sqrt_eq_rpow] at hh
  rw [hh,ENNReal.toReal_ofReal (Real.sqrt_nonneg _),Real.sq_sqrt]
  exact integral_nonneg (fun _ => sq_nonneg _)

lemma integral_norm_sq_le_of_eLpNorm {f : Ω → E}
    (_hm : AEStronglyMeasurable f μ) {B : ℝ≥0∞} (hB : B≠⊤)
    (hb : eLpNorm f 2 μ≤B) :
    Integrable (fun x => ‖f x‖^2) μ ∧ (∫x,‖f x‖^2 ∂μ)≤B.toReal^2 := by
  have hf : MemLp f 2 μ := lt_of_le_of_lt hb (lt_top_iff_ne_top.mpr hB)
  refine ⟨hf.integrable_norm_pow (by norm_num : (2:ℕ)≠0),?_⟩
  rw [integral_norm_sq_eq_eLpNorm f hf]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono hB hb) 2
end RMSIntegral

lemma gaussian_operator_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [SFinite μ] {d : ℕ} (A : Ω → Point d →L[ℝ] Point d)
    (hA : Measurable A) (hi : Integrable (fun y => ‖A y‖^2) μ) {B : ℝ}
    (hB : (∫y,‖A y‖^2 ∂μ)≤B) :
    Integrable (fun p : Ω × Point d => ‖A p.1 p.2‖^2) (μ.prod (ProbabilityTheory.stdGaussian (Point d))) ∧
      (∫p : Ω × Point d,‖A p.1 p.2‖^2 ∂(μ.prod (ProbabilityTheory.stdGaussian (Point d))))≤B*d := by
  have hg : Integrable (fun z : Point d => ‖z‖^2) (ProbabilityTheory.stdGaussian (Point d)) := by
    simpa only [id_eq] using
      (ProbabilityTheory.IsGaussian.memLp_two_id (μ:=ProbabilityTheory.stdGaussian (Point d))).integrable_norm_pow
        (by norm_num : (2:ℕ)≠0)
  have hiB := hi.mul_prod hg
  have hb (p : Ω × Point d) : ‖A p.1 p.2‖^2≤‖A p.1‖^2*‖p.2‖^2 := by
    rw [←mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.le_opNorm _ _) 2
  have hm : Measurable (fun p : Ω × Point d => A p.1 p.2) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp
      ((hA.comp measurable_fst).prodMk measurable_snd)
  have his : Integrable (fun p : Ω × Point d => ‖A p.1 p.2‖^2)
      (μ.prod (ProbabilityTheory.stdGaussian (Point d))) :=
    hiB.mono' (hm.norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs,abs_sq] using hb p))
  refine ⟨his,?_⟩
  calc
    _ ≤ ∫p : Ω × Point d,‖A p.1‖^2*‖p.2‖^2 ∂(μ.prod (ProbabilityTheory.stdGaussian (Point d))) :=
      integral_mono his hiB hb
    _ = (∫y,‖A y‖^2 ∂μ)*d := by rw [integral_prod_mul (fun y => ‖A y‖^2) (fun z : Point d => ‖z‖^2),stdGaussian_sq_norm]
    _ ≤ _ := mul_le_mul_of_nonneg_right hB (Nat.cast_nonneg _)
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Filter MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal ENNReal RealInnerProductSpace

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1)

def terminalActionChain : ℕ → ℝ × (Point d × Point d) → Point d
  | 0 => fun p => (terminalJacobian hF x hr hl hT0.le hT1 (p.1,p.2.1)-
      ContinuousLinearMap.id ℝ (Point d)) p.2.2
  | n+1 => fun p => TimeJet.jet (terminalJacobian hF x hr hl hT0.le hT1) (n+1) (p.1,p.2.1) p.2.2

lemma terminalActionChain_smooth (n : ℕ) :
    ContDiff ℝ (⊤:ℕ∞) (terminalActionChain hF x hr hl hT0 hT1 n) := by
  cases n with
  | zero => exact (((terminalJacobian_smooth hF x hr hl hT0.le hT1).comp
      (contDiff_fst.prodMk contDiff_snd.fst)).sub contDiff_const).clm_apply contDiff_snd.snd
  | succ n => exact ((TimeJet.smooth (terminalJacobian_smooth hF x hr hl hT0.le hT1) (n+1)).comp
      (contDiff_fst.prodMk contDiff_snd.fst)).clm_apply contDiff_snd.snd

lemma terminalActionChain_hasDerivAt (n : ℕ) (t : ℝ) (p : Point d × Point d) :
    HasDerivAt (fun s => terminalActionChain hF x hr hl hT0 hT1 n (s,p))
      (terminalActionChain hF x hr hl hT0 hT1 (n+1) (t,p)) t := by
  have hd (n : ℕ) := (TimeJet.hasDerivAt _
    (terminalJacobian_smooth hF x hr hl hT0.le hT1) n t p.1).clm_apply (hasDerivAt_const t p.2)
  cases n with
  | zero =>
    have hh := (hd 0).sub_const p.2
    simpa only [terminalActionChain,TimeJet.jet,Function.comp_apply,
      sub_apply,ContinuousLinearMap.id_apply,map_zero,
      add_zero] using hh
  | succ n =>
    simpa only [terminalActionChain,map_zero,add_zero] using hd (n+1)

include hlam in
lemma terminalActionChain_first_zero (p : Point d × Point d) :
    terminalActionChain hF x hr hl hT0 hT1 1 (0,p)=0 := by
  exact (terminalActionChain_hasDerivAt hF x hr hl hT0 hT1 0 0 p).unique
    (terminalJacobian_action_initial_deriv hF x hr hlam hl hT0 hT1 p.1 p.2)

include hlam in

theorem terminalActionChain_sq (hd : 1≤d) (n : ℕ) (t : Icc (0:ℝ) T) :
    let μ := (interpolationLaw F x r T).prod (stdGaussian (Point d))
    let b := (r*((lam:ℝ)*r)*Real.exp (Real.pi^2/4))*
      ((TensorSum.terminalQ n).val.momentBudget d 0 2).toReal*
      ((Real.sqrt (1-(t:ℝ)^2))⁻¹)^(2*n)
    Integrable (fun p => ‖terminalActionChain hF x hr hl hT0 hT1 (n+1) (t,p)‖^2) μ ∧
      (∫p,‖terminalActionChain hF x hr hl hT0 hT1 (n+1) (t,p)‖^2 ∂μ)≤b^2*d := by
  dsimp only
  let := interpolationLaw_probability hF x hr.le (by linarith) T
  let A := fun y => TimeJet.jet (terminalJacobian hF x hr hl hT0.le hT1) (n+1) (t,y)
  have hAc : Continuous A := (TimeJet.smooth
    (terminalJacobian_smooth hF x hr hl hT0.le hT1) (n+1)).continuous.comp
      (continuous_const.prodMk continuous_id)
  have he : A=fun y => iteratedDeriv (n+1)
      (fun s => terminalJacobian hF x hr hl hT0.le hT1 (s,y)) t :=
    funext (fun y => TimeJet.eq_iteratedDeriv _
      (terminalJacobian_smooth hF x hr hl hT0.le hT1) (n+1) t y)
  let B : ℝ≥0∞ := ENNReal.ofReal (r*((lam:ℝ)*r)*Real.exp (Real.pi^2/4))*
    (TensorSum.terminalQ n).val.momentBudget d 0 2*
      ENNReal.ofReal ((Real.sqrt (1-(t:ℝ)^2))⁻¹)^(2*n)
  have hB : B≠⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (TensorSum.momentBudget_ne_top _ _ _ _))
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hb : eLpNorm A 2 (interpolationLaw F x r T)≤B := by
    rw [he]
    exact terminalJacobian_iteratedDeriv_eLpNorm hF x hr hlam hl hT0 hT1 hd n t
      (by norm_num) (by norm_num)
  have hi := RMSIntegral.integral_norm_sq_le_of_eLpNorm hAc.aestronglyMeasurable hB hb
  have hh := gaussian_operator_sq A hAc.measurable hi.1 hi.2
  simpa only [B,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity : 0≤r*((lam:ℝ)*r)*Real.exp (Real.pi^2/4)),
    ENNReal.toReal_ofReal (by positivity : 0≤(Real.sqrt (1-(t:ℝ)^2))⁻¹),
    terminalActionChain,A] using hh

end LogConcaveSampling

end

end

end OAI
