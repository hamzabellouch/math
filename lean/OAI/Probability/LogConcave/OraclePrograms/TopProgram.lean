import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.Fresh
import OAI.Probability.LogConcave.OraclePrograms.IndependentSeq
import OAI.Probability.LogConcave.Sampling.AverageLipschitz

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeasureTheory ProbabilityTheory Function
open scoped Classical NNReal

variable {d : ℕ}

def topProgram (S : ReservedProgram d) (h : ℝ) (N J : ℕ) :=
  (Program.fresh (fun _ => proximalProgram S h) N).independentSeq
    (Program.fresh (fun j => halvingProgram S (descentScale h j)) J)

def topSeedLaw (S : ReservedProgram d) (N J : ℕ) :=
  ((Measure.dirac (0:Point d)).prod (Measure.pi (fun _ : Fin N => gaussianTape d S.full.slots))).prod
    (Measure.pi (fun _ : Fin J => gaussianTape d S.full.slots))

instance topSeedLaw_probability (S : ReservedProgram d) (N J : ℕ) :
    IsProbabilityMeasure (topSeedLaw S N J) := by unfold topSeedLaw; infer_instance

lemma topProgram_law (S : ReservedProgram d) (h : ℝ) (N J : ℕ)
    {V : Point d → ℝ} (hV : Admissible V) :
    (topSeedLaw S N J).map ((topProgram S h N J).run V)=
      changingChain (fun j => approximateHalvingKernel S (descentScale h j) V hV)
        (markovChain (approximateProximalKernel S h V hV) (Measure.dirac 0) N) J := by
  let (j : ℕ) : IsMarkovKernel (approximateHalvingKernel S (descentScale h j) V hV) :=
    approximateHalvingKernel_markov _ _ _
  let := approximateProximalKernel_markov S h hV
  have hVm := hV.continuous_firstOrderReply.measurable
  rw [topProgram,topSeedLaw,Program.independentSeq_law _ _ hVm,
    Program.fresh_law (fun _ => proximalProgram S h) hVm]
  rw [stateLaw_eq_changingChain _ _ _ (fun _ => (proximalProgram S h).measurable_run V hVm)
    (fun _ => approximateProximalKernel S h V hV) (fun _ => approximateProximalKernel_apply S h hV),
    changingChain_constant]
  rw [Program.fresh_law _ hVm]
  exact stateLaw_eq_changingChain _ _ _
    (fun j => (halvingProgram S (descentScale h j)).measurable_run V hVm)
    _ (fun j => approximateHalvingKernel_program S (descentScale h j) hV) J

lemma affine_correct_from_uniform (S : ℝ → ℝ → ReservedProgram d) {q K e ηmin : ℝ}
    (hc : ∀{F : Point d → ℝ} {lam : ℝ≥0},Primitive F lam → 0<lam → (lam:ℝ)≤1 →
      SampleCorrect F lam q K e ηmin S)
    {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0<h) (hh1 : 2*h≤1) (y : Point d) :
    SampleCorrect (affinePotential V y (Real.sqrt h)) (2*h) q K e ηmin S := by
  have hp : (0:ℝ)<2*(Real.sqrt h)^2 := by rw [Real.sq_sqrt hh.le]; positivity
  have hl : 2*(Real.sqrt h)^2≤1 := by rwa [Real.sq_sqrt hh.le]
  have he := hc (hV.affinePrimitive y (Real.sqrt h)) (show (0:ℝ≥0)<⟨2*(Real.sqrt h)^2,by positivity⟩ from hp) hl
  change SampleCorrect _ (2*(Real.sqrt h)^2) q K e ηmin S at he
  simpa only [Real.sq_sqrt hh.le] using he

theorem topProgram_accuracy (S : ℝ → ℝ → ReservedProgram d) {q K e ηmin h : ℝ}
    (hh : 0<h) (hq : 2*h≤q) (hq1 : q<1) (he : 0≤e) (hη : ηmin≤1)
    (hres : (S 1 1).reserve=1/2)
    (hc : ∀{F : Point d → ℝ} {lam : ℝ≥0},Primitive F lam → 0<lam → (lam:ℝ)≤1 →
      SampleCorrect F lam q K e ηmin S)
    (n J : ℕ) {V : Point d → ℝ} (hV : Admissible V) :
    TVAtMost ((topSeedLaw (S 1 1) (n+1) J).map ((topProgram (S 1 1) h (n+1) J).run V))
      (gibbs V)
      (((n+1)*18+J*10)*e*Real.sqrt d+
        ((1+Real.sqrt h)*Real.sqrt d)/((1+h)^(n+1)*Real.sqrt h)+
        2*(2*Real.sqrt (descentScale h J)+descentScale h J)*d) := by
  let T := S 1 1
  have hh1 : h≤1 := by linarith
  have hs : Real.sqrt h≤1 := by simpa using Real.sqrt_le_sqrt hh1
  have hloc := approximateProximalKernel_tv S hV hh hq hq1 he hη hres
    (affine_correct_from_uniform S hc hV hh (by linarith))
  let := approximateProximalKernel_markov T h hV
  let := proximalKernel_markov hV hh
  let := noisedLaw_probability hV h
  let := noisedLaw_probability hV (descentScale h J)
  let (j : ℕ) : IsMarkovKernel (approximateHalvingKernel T (descentScale h j) V hV) :=
    approximateHalvingKernel_markov _ _ _
  have hp := proximal_chain_perturbation hV hh (approximateProximalKernel T h V hV)
    (a:=2*e*Real.sqrt d) (b:=4*e*Real.sqrt h) (by positivity) (by positivity)
    (fun x => by convert! hloc x using 1; ring) (n+1)
  have hp' : TVAtMost (markovChain (approximateProximalKernel T h V hV) (Measure.dirac 0) (n+1))
      (markovChain (proximalKernel V hV h) (Measure.dirac 0) (n+1))
      ((n+1)*(18*e*Real.sqrt d)) := by
    apply hp.mono
    push_cast
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hss : Real.sqrt h*(1+Real.sqrt h)≤2 := by nlinarith [Real.sqrt_nonneg h]
    nlinarith [mul_le_mul_of_nonneg_right hss (by positivity : 0≤e*Real.sqrt d)]
  have hm := hp'.trans (proximal_chain_mixing hV hh n)
  have hd := halving_chain_error hV hh hh1 he
    (fun j => approximateHalvingKernel T (descentScale h j) V hV)
    (fun j x => approximateHalvingKernel_tv S hV (descentScale_pos hh j)
      (by linarith [descentScale_le hh.le j]) hq1 he hη hres
      (affine_correct_from_uniform S hc hV (descentScale_pos hh j)
        (by linarith [descentScale_le hh.le j])) x) J
  have ht := ((changingChain_tv _ hm J).trans hd).trans
    (noisedLaw_tv hV (descentScale_pos hh J))
  rw [topProgram_law _ _ _ _ hV]
  apply ht.mono
  ring_nf
  rfl

end LogConcaveSampling.OracleCompiler

end

end

end OAI
