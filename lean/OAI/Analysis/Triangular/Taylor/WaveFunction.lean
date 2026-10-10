import OAI.Analysis.Triangular.Schwartz.InputCLM
import OAI.Analysis.Triangular.Schwartz.FourierCLM
import OAI.Analysis.Triangular.Construction.CurvatureBoxes
import OAI.Analysis.Triangular.Taylor.FiniteTaylorIdentity

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

def wavePhaseFunction (q br : Fin 2) : C(Spectrum,ℂ) :=
  if br.val=0 then frequencyFunction - ContinuousMap.const _ ((Real.pi*(damping q-h):ℝ):ℂ)
  else zetaFunction (damping q) h (damping_pos q)
def waveAmplitudeFunction (q br : Fin 2) : C(Spectrum,ℂ) :=
  if br.val=0 then 1 else lambdaFunction (damping q) (damping_pos q)
lemma wavePhaseFunction_apply (q br : Fin 2) (t : Spectrum) :
    wavePhaseFunction q br t=taylorPhase q br t.val := by
  fin_cases br <;> rfl
lemma waveAmplitudeFunction_apply (q br : Fin 2) (t : Spectrum) :
    waveAmplitudeFunction q br t=taylorAmplitude q br t.val := by
  fin_cases br <;> rfl

def waveFunctionJet (q br : Fin 2) (k : ℕ) (s : ℂ) : C(Spectrum,ℂ) :=
  waveAmplitudeFunction q br * NormedSpace.exp (s • wavePhaseFunction q br) * wavePhaseFunction q br^k
lemma waveFunctionJet_apply (q br : Fin 2) (k : ℕ) (s : ℂ) (t : Spectrum) :
    waveFunctionJet q br k s t=finiteWaveJet q br t.val k s := by
  simp only [waveFunctionJet,ContinuousMap.mul_apply,ContinuousMap.pow_apply,
    exponential_apply,ContinuousMap.smul_apply,smul_eq_mul,wavePhaseFunction_apply,
    waveAmplitudeFunction_apply,finiteWaveJet,mul_comm s]
lemma hasDerivAt_waveFunctionJet (q br : Fin 2) (k : ℕ) (s : ℂ) :
    HasDerivAt (waveFunctionJet q br k) (waveFunctionJet q br (k+1) s) s := by
  have hh := ((hasDerivAt_exp_smul_const (wavePhaseFunction q br) s).const_mul
    (waveAmplitudeFunction q br)).mul_const ((wavePhaseFunction q br)^k)
  convert hh using 1 <;> try simp only [waveFunctionJet,pow_succ]
  all_goals first | rfl | (ext t; simp [ContinuousMap.mul_apply,ContinuousMap.pow_apply]; ring)
lemma differentiable_waveFunctionJet (q br : Fin 2) (k : ℕ) :
    Differentiable ℂ (waveFunctionJet q br k) := fun s => (hasDerivAt_waveFunctionJet q br k s).differentiableAt

lemma norm_finiteWaveJet_two (q br : Fin 2) (s t : ℝ) :
    ‖finiteWaveJet q br t 2 s‖=curvatureWave q br s t := by
  simp only [finiteWaveJet,norm_mul,norm_pow,Complex.norm_exp,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero,curvatureWave]
  ring
lemma waveFunctionJet_uniform (q br : Fin 2) (s : ℝ) {M : ℝ} (hM : 0≤M)
    (hb : ∀ t : ℝ, |t|≤5/6 → curvatureWave q br s t≤M) :
    ‖waveFunctionJet q br 2 s‖≤M := by
  apply (ContinuousMap.norm_le _ hM).mpr
  intro t
  rw [waveFunctionJet_apply,norm_finiteWaveJet_two]
  exact hb t.val (abs_le.mpr t.property)

def inputJJet (a : InputCoefficients) (br : Fin 2) (k : ℕ) (s : ℂ) : ℂ :=
  tailSpectral a (waveFunctionJet 0 br k s)+finiteSpectral a (waveFunctionJet 1 br k s)
def pairJJet (a₁ a₂ : InputCoefficients) (k : ℕ) (s : ℂ) : ℂ :=
  inputJJet a₁ 0 k s+inputJJet a₂ 1 k s
def pairJ (a₁ a₂ : InputCoefficients) (s : ℝ) : ℝ := (pairJJet a₁ a₂ 0 s).re
lemma hasDerivAt_inputJJet (a : InputCoefficients) (br : Fin 2) (k : ℕ) (s : ℂ) :
    HasDerivAt (inputJJet a br k) (inputJJet a br (k+1) s) s := by
  exact ((tailSpectral a).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_waveFunctionJet 0 br k s)).add
    ((finiteSpectral a).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_waveFunctionJet 1 br k s))
lemma hasDerivAt_pairJJet (a₁ a₂ : InputCoefficients) (k : ℕ) (s : ℂ) :
    HasDerivAt (pairJJet a₁ a₂ k) (pairJJet a₁ a₂ (k+1) s) s :=
  (hasDerivAt_inputJJet a₁ 0 k s).add (hasDerivAt_inputJJet a₂ 1 k s)
lemma pairJJet_iterated (a₁ a₂ : InputCoefficients) (k : ℕ) :
    (fun s : ℝ => (pairJJet a₁ a₂ k s).re)=iteratedDeriv k (pairJ a₁ a₂) := by
  induction k with
  | zero => rfl
  | succ k hk =>
    rw [iteratedDeriv_succ,←hk]
    exact funext fun s => ((hasDerivAt_pairJJet a₁ a₂ k s).real_of_complex).deriv.symm
lemma pairJ_contDiff (a₁ a₂ : InputCoefficients) : ContDiff ℝ ⊤ (pairJ a₁ a₂) := by
  have hh : Differentiable ℂ (pairJJet a₁ a₂ 0) := fun s => (hasDerivAt_pairJJet a₁ a₂ 0 s).differentiableAt
  exact hh.contDiff.real_of_complex
end AtomicTriangular.Construction
end

end OAI
