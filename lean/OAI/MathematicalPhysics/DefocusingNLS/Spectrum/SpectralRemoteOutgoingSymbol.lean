import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteStateSymbol
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteIncomingDecay
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingTail

namespace OAI

/-! Canonical outgoing columns give individual logarithmic symbols for
the actual harmonic eigenpair coordinates. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem spectralRemote_physical_value_symbol
    (nuPlus nuMinus : ℂ) (sigma : ℝ) (Y : ℝ → SpectralRemoteSpace)
    (hp : HasLogJetBound 0 (fun t => (Y t).1.1))
    (hm : HasLogJetBound 0 (fun t => (Y t).2.1))
    (hsp : nuPlus.re ≤ sigma) (hsm : nuMinus.re ≤ sigma) :
    HasLogJetBound sigma (fun t => (spectralPhysicalPair nuPlus nuMinus Y (Real.exp t)).1.1) ∧
      HasLogJetBound sigma (fun t => (spectralPhysicalPair nuPlus nuMinus Y (Real.exp t)).2.1) := by
  constructor
  · simpa only [spectralPhysicalPair,spectralPhysicalJet,Real.log_exp] using
      (homogeneousPhysicalProfile_logJetBound nuPlus _ hp).mono hsp
  · simpa only [spectralPhysicalPair,spectralPhysicalJet,Real.log_exp] using
      (homogeneousPhysicalProfile_logJetBound nuMinus _ hm).mono hsm

theorem spectralRemote_outgoing_span_symbol
    (nuPlus nuMinus : ℂ) (sigma : ℝ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (Yp Ym : ℝ → SpectralRemoteSpace) (a : ℂ × ℂ)
    (hpp : HasLogJetBound 0 (fun t => (Yp t).1.1))
    (hpm : HasLogJetBound 0 (fun t => (Yp t).2.1))
    (hmp : HasLogJetBound 0 (fun t => (Ym t).1.1))
    (hmm : HasLogJetBound 0 (fun t => (Ym t).2.1))
    (hsp : nuPlus.re ≤ sigma) (hsm : nuMinus.re ≤ sigma)
    (hspan : ∀ᶠ r in atTop, harmonicRadialState f g r =
      a.1 • spectralPhysicalPair nuPlus nuMinus Yp r+
      a.2 • spectralPhysicalPair nuPlus nuMinus Ym r) :
    HasLogJetBound sigma (spectralRemoteEigenpairState f g) := by
  obtain ⟨hpp',hpm'⟩ := spectralRemote_physical_value_symbol nuPlus nuMinus sigma Yp hpp hpm hsp hsm
  obtain ⟨hmp',hmm'⟩ := spectralRemote_physical_value_symbol nuPlus nuMinus sigma Ym hmp hmm hsp hsm
  have hsumP := (hpp'.const_mul a.1).add (hmp'.const_mul a.2)
  have hsumM := (hpm'.const_mul a.1).add (hmm'.const_mul a.2)
  have heP : (fun t => a.1*(spectralPhysicalPair nuPlus nuMinus Yp (Real.exp t)).1.1+
      a.2*(spectralPhysicalPair nuPlus nuMinus Ym (Real.exp t)).1.1) =ᶠ[atTop]
      (fun t => f (Real.exp t)) := by
    filter_upwards [Real.tendsto_exp_atTop.eventually hspan] with t ht
    have hh := congrArg (fun z : SpectralRemoteSpace => z.1.1) ht
    simpa only [harmonicRadialState,Prod.fst_add,Prod.smul_fst,smul_eq_mul] using hh.symm
  have heM : (fun t => a.1*(spectralPhysicalPair nuPlus nuMinus Yp (Real.exp t)).2.1+
      a.2*(spectralPhysicalPair nuPlus nuMinus Ym (Real.exp t)).2.1) =ᶠ[atTop]
      (fun t => g (Real.exp t)) := by
    filter_upwards [Real.tendsto_exp_atTop.eventually hspan] with t ht
    have hh := congrArg (fun z : SpectralRemoteSpace => z.2.1) ht
    simpa only [harmonicRadialState,Prod.snd_add,Prod.fst_add,Prod.smul_snd,Prod.smul_fst,smul_eq_mul] using hh.symm
  exact spectralRemoteEigenpairState_symbol sigma f g hf hg
    (hsumP.eventually_congr heP) (hsumM.eventually_congr heM)

end DefocusingNLS

end OAI
