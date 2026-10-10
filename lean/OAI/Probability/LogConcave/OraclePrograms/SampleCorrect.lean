import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.FullTape

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler.CircuitParameters
open MeanTree Coupling MeasureTheory ProbabilityTheory
open scoped Classical NNReal

variable (C : CircuitParameters) {d : ℕ}

theorem sampleFrom_correct {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {q Kf Ki ef ei en ηmin : ℝ} (hd : 1≤d) (hlam : (lam:ℝ)≤1)
    (hq : 0≤q) (hql : q≤1/4) (hR : Real.sqrt (1-C.T^2)≤ηmin)
    (hD : 1≤C.D) (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hKf : 0≤Kf) (hKi : 0≤Ki) (hef : 0<ef) (hei : 0≤ei) (hen : 0≤en)
    (hsmall : 2*C.A*q*(2*Real.pi+2)≤1) (hcon : 4*C.A*q*Ki≤1)
    (Mf Mi : ℝ → ℝ → SeedProgram d) (B : ℕ) (hBD : (B:ℝ)≤C.D^2)
    (hbudget : ∀(s : Bool) r τ,MeanBudget B r ((if s then Mf else Mi) r τ))
    (hf : MeanCorrect F lam ((1+4*C.Af)*q) Kf ef Mf)
    (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi)
    (hnum : C.SampleNumericalReady hF q en) :
    SampleCorrect F lam q (C.Af*C.depthBound*Kf)
      (C.sampleError C.depthBound Kf q ei ef en) ηmin (C.sampleFrom Mf Mi) := by
  have hA0 : 0<C.A := hA ▸ C.actualA_pos
  have hAf0 : 0<C.Af := hAf ▸ C.actualAf_pos
  have small {r η : ℝ} (hs : SampleSize lam q r η) :=
    physical_small_of_scaled hA0.le hq hKi
      (show 0≤(lam:ℝ)*C.sampleCenterBudget r by unfold sampleCenterBudget; positivity)
      (C.sampleCenter_scaled hs lam.coe_nonneg hA0.le) hsmall hcon
  constructor
  · intro r η hs hη x y g
    have he := C.sampleFrom_lipschitz hs (hR.trans hη) (by linarith) hA hAf hKf hKi
      (small hs).2.2 Mf Mi hf hi x y g
    apply he.trans
    have hdep : (depth (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1):ℝ)≤C.depthBound :=
      by exact_mod_cast C.sampleTree_depth (d:=d) r η hs.2.2.1 hs.2.2.2.1
    have hh := mul_le_mul_of_nonneg_right hdep
      (show 0≤(lam:ℝ)*r*C.Af*Kf*‖x-y‖ by positivity [hs.1])
    nlinarith only [hh]
  · intro r η hs hη x
    have hL : (lam:ℝ)*r≤1 := (mul_le_of_le_one_left hs.1.le hlam).trans hs.2.1
    have hlr : (lam:ℝ)*r^2≤1/2 := by
      have hh := hs.2.2.2.2.trans (mul_le_of_le_one_right hq hs.2.2.2.1)
      linarith
    have hp := C.sampleFrom_squared hF hd hs hql hL (hR.trans hη) hD hA hAf hKf hKi hef hei
      (small hs).1 (small hs).2.1 Mf Mi B hBD hbudget hf hi x hlr
      (hnum x r η hs hlr).1 (hnum x r η hs hlr).2
    apply hp.mono
    let dep := (depth (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1):ℝ)
    let a := 2*(1+dep)*(C.Af*Kf*q*ei+ef)
    have hdep : dep≤C.depthBound := by dsimp only [dep]; exact_mod_cast C.sampleTree_depth (d:=d) r η hs.2.2.1 hs.2.2.2.1
    have hdep0 : 0≤dep := by dsimp [dep]; positivity
    have ha : 0≤a := by dsimp [a]; positivity
    have ha' : a≤C.compilerError C.depthBound Kf q ei ef := by
      unfold compilerError
      dsimp only [a]
      have hh : 0≤C.Af*Kf*q*ei+ef := by positivity
      nlinarith [mul_nonneg hh (sub_nonneg.mpr hdep)]
    apply (sample_error_envelope hs.2.2.1.le hs.2.2.2.1 ha hen).trans
    have he : 20*a+2*en≤C.sampleError C.depthBound Kf q ei ef en := by unfold sampleError; linarith
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity : 0≤20*a+2*en) he 2) (sq_nonneg _)
end LogConcaveSampling.OracleCompiler.CircuitParameters

end

end

end OAI
