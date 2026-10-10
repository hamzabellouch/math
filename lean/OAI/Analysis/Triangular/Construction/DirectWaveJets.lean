import OAI.Analysis.Triangular.Construction.TailEnumeration
import OAI.Analysis.Triangular.Taylor.WaveFunction
import OAI.Analysis.Triangular.Construction.NodeJets
import OAI.Analysis.Triangular.Construction.FiniteJets

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
lemma waveFunctionJet_direct_zero (q : Fin 2) (s : ℂ) :
    waveFunctionJet q 0 0 s=exp (-(Real.pi:ℂ)*(damping q-h)*s) • phaseFunction s := by
  ext t
  rw [waveFunctionJet_apply]
  simp only [finiteWaveJet,taylorAmplitude,taylorPhase,Fin.val_zero,↓reduceIte,pow_zero,mul_one,one_mul,
    ContinuousMap.smul_apply,smul_eq_mul,phaseFunction]
  simp only [ofReal_mul,ofReal_sub,ContinuousMap.coe_mk]
  rw [show (I*Real.pi*(t.val:ℂ)-(Real.pi:ℂ)*(damping q-h))*s=
    -(Real.pi:ℂ)*(damping q-h)*s+I*Real.pi*(t.val:ℂ)*s by ring,exp_add]
lemma waveFunctionJet_zero_phase (s : ℂ) : waveFunctionJet 0 0 0 s=phaseFunction s := by
  rw [waveFunctionJet_direct_zero]
  simp only [damping,Fin.val_zero,↓reduceIte,sub_self,mul_zero,zero_mul,exp_zero,one_smul]
lemma hasDerivAt_phaseFunction (s : ℂ) : HasDerivAt phaseFunction (waveFunctionJet 0 0 1 s) s := by
  have he : phaseFunction=waveFunctionJet 0 0 0 := (funext waveFunctionJet_zero_phase).symm
  rw [he]
  exact hasDerivAt_waveFunctionJet 0 0 0 s
lemma spectralC_direct (n : Node) (s : ℂ) :
    spectralCCLM n (waveFunctionJet 0 0 0 s)=cBasis n s ∧
    spectralCCLM n (waveFunctionJet 0 0 1 s)=deriv (cBasis n) s := by
  constructor
  · rw [waveFunctionJet_zero_phase,spectralCCLM_apply,spectralC_phase]
  · have he : (fun s => spectralCCLM n (phaseFunction s))=cBasis n := funext fun s => by rw [spectralCCLM_apply,spectralC_phase]
    have hh := ((spectralCCLM n).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_phaseFunction s)).deriv
    simp only [Function.comp_def] at hh
    rw [he] at hh
    exact hh.symm
lemma spectralD_direct (n : Node) (s : ℂ) :
    spectralDCLM n (waveFunctionJet 0 0 0 s)=dBasis n s ∧
    spectralDCLM n (waveFunctionJet 0 0 1 s)=deriv (dBasis n) s := by
  constructor
  · rw [waveFunctionJet_zero_phase,spectralDCLM_apply,spectralD_phase]
  · have he : (fun s => spectralDCLM n (phaseFunction s))=dBasis n := funext fun s => by rw [spectralDCLM_apply,spectralD_phase]
    have hh := ((spectralDCLM n).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_phaseFunction s)).deriv
    simp only [Function.comp_def] at hh
    rw [he] at hh
    exact hh.symm
lemma spectralP_direct (s : ℂ) :
    spectralPCLM (waveFunctionJet 0 0 0 s)=P s ∧
    spectralPCLM (waveFunctionJet 0 0 1 s)=deriv P s := by
  constructor
  · rw [waveFunctionJet_zero_phase,spectralPCLM_apply,spectralP_phase]
  · have he : (fun s => spectralPCLM (phaseFunction s))=P := funext fun s => by rw [spectralPCLM_apply,spectralP_phase]
    have hh := (spectralPCLM.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_phaseFunction s)).deriv
    simp only [Function.comp_def] at hh
    rw [he] at hh
    exact hh.symm
lemma atomC_direct (a : Fin 15) (s : ℂ) :
    atomSpectral (FiniteCertificate.cCoefficient a) (waveFunctionJet 0 0 0 s)=finiteC a s ∧
    atomSpectral (FiniteCertificate.cCoefficient a) (waveFunctionJet 0 0 1 s)=deriv (finiteC a) s := by
  constructor
  · rw [waveFunctionJet_zero_phase,atomSpectral_finiteC_phase]
  · have he : (fun s => atomSpectral (FiniteCertificate.cCoefficient a) (phaseFunction s))=finiteC a := funext (atomSpectral_finiteC_phase a)
    have hh := ((atomSpectral (FiniteCertificate.cCoefficient a)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_phaseFunction s)).deriv
    simp only [Function.comp_def] at hh
    rw [he] at hh
    exact hh.symm
lemma atomD_direct (a : Fin 15) (s : ℂ) :
    atomSpectral (FiniteCertificate.dCoefficient a) (waveFunctionJet 0 0 0 s)=finiteD a s ∧
    atomSpectral (FiniteCertificate.dCoefficient a) (waveFunctionJet 0 0 1 s)=deriv (finiteD a) s := by
  constructor
  · rw [waveFunctionJet_zero_phase,atomSpectral_finiteD_phase]
  · have he : (fun s => atomSpectral (FiniteCertificate.dCoefficient a) (phaseFunction s))=finiteD a := funext (atomSpectral_finiteD_phase a)
    have hh := ((atomSpectral (FiniteCertificate.dCoefficient a)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_phaseFunction s)).deriv
    simp only [Function.comp_def] at hh
    rw [he] at hh
    exact hh.symm
lemma waveFunctionJet_direct_one (q : Fin 2) (s : ℂ) :
    waveFunctionJet q 0 1 s= exp (-(Real.pi:ℂ)*(damping q-h)*s) •
      (waveFunctionJet 0 0 1 s-(Real.pi*(damping q-h):ℂ) • phaseFunction s) := by
  have he : waveFunctionJet q 0 0 = fun t => exp (-(Real.pi:ℂ)*(damping q-h)*t) • phaseFunction t := funext (waveFunctionJet_direct_zero q)
  have hh := (((hasDerivAt_id s).const_mul (-(Real.pi:ℂ)*(damping q-h))).cexp.smul (hasDerivAt_phaseFunction s)).deriv
  have hj := (hasDerivAt_waveFunctionJet q 0 0 s).deriv
  rw [he] at hj
  change deriv (fun t => exp (-(Real.pi:ℂ)*(damping q-h)*t) • phaseFunction t) s = _ at hh
  rw [←hj,hh]
  simp only [id_eq,mul_one]
  module
lemma cBasis_deriv_re (n : Node) : (deriv (cBasis n) n.val).re=Q n.val*D n.val := by
  have hQ : Q n.val≠0 := (lt_trans (by norm_num) (FiniteCertificate.Q_node_bounds n.val n.property.2).1).ne'
  have hh := cBasis_deriv_at_node n
  unfold D
  field_simp
  linarith
lemma finiteC_deriv_re (a : Fin 15) (n : ℤ) (hn : n%36=residue a) :
    (deriv (finiteC a) n).re=Q n*D n := by
  have hmem : n%36∈residues := by rw [hn]; exact residue_mem a
  have hQ : Q n≠0 := (lt_trans (by norm_num) (FiniteCertificate.Q_node_bounds n hmem).1).ne'
  have hh := (finiteC_matching_jets a n hn).2
  unfold D
  field_simp
  linarith
end AtomicTriangular.Construction
end

end OAI
