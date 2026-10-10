import Mathlib
import OAI.Analysis.Conductivity.Variational.VoltagePoincare

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

abbrev VoltageJetSpace (μ : Measure Coord3) (U : Set Coord3) :=
  Lp (Fin 2 → ℝ) 2 (μ.restrict U) × Lp FieldVector 2 (μ.restrict U)

def compactVoltageJets (μ : Measure Coord3) (U : Set Coord3) : Set (VoltageJetSpace μ U) :=
  {z | ∃ (v : Coord3 → Fin 2 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) v ∧
    HasCompactSupport v ∧ tsupport v ⊆ U ∧
    ∃ (hm : MemLp v 2 (μ.restrict U)) (hg : MemLp (voltageGradient v) 2 (μ.restrict U)),
      z = (hm.toLp _,hg.toLp _)}

lemma voltageGradient_zero : voltageGradient (0 : Coord3 → Fin 2 → ℝ) = 0 := by
  funext x
  change gradientVectorCLM (fderiv ℝ (0 : Coord3 → Fin 2 → ℝ) x) = 0
  simp only [fderiv_zero,Pi.zero_apply,map_zero]

lemma voltageGradient_smul (c : ℝ) {v : Coord3 → Fin 2 → ℝ} (hv : Differentiable ℝ v) :
    voltageGradient (c • v) = c • voltageGradient v := by
  funext x
  simp only [voltageGradient,fderiv_const_smul (hv x),map_smul,Pi.smul_apply]

lemma compactVoltageJets_zero (μ : Measure Coord3) (U : Set Coord3) :
    (0 : VoltageJetSpace μ U) ∈ compactVoltageJets μ U := by
  refine ⟨0,contDiff_const,HasCompactSupport.zero,?_,MemLp.zero,?_,?_⟩
  · simp
  · rw [voltageGradient_zero]; exact MemLp.zero
  · simp only [voltageGradient_zero,MemLp.toLp_zero,Prod.zero_eq_mk]

lemma compactVoltageJets_add (μ : Measure Coord3) (U : Set Coord3)
    {z w : VoltageJetSpace μ U} (hz : z ∈ compactVoltageJets μ U)
    (hw : w ∈ compactVoltageJets μ U) : z+w ∈ compactVoltageJets μ U := by
  obtain ⟨v,hv,hvc,hvs,hvm,hvg,rfl⟩ := hz
  obtain ⟨f,hf,hfc,hfs,hfm,hfg,rfl⟩ := hw
  have he : voltageGradient (v+f) = voltageGradient v+voltageGradient f :=
    funext fun x => voltageGradient_add (hv.differentiable (by simp) x) (hf.differentiable (by simp) x)
  have hmg : MemLp (voltageGradient (v+f)) 2 (μ.restrict U) := by rw [he]; exact hvg.add hfg
  refine ⟨v+f,hv.add hf,hvc.add hfc,(tsupport_add v f).trans (union_subset hvs hfs),
    hvm.add hfm,hmg,?_⟩
  apply Prod.ext
  · exact (MemLp.toLp_add hvm hfm).symm
  · change hvg.toLp _ + hfg.toLp _ = hmg.toLp _
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => congrFun he x |>.symm)

lemma compactVoltageJets_smul (μ : Measure Coord3) (U : Set Coord3)
    (c : ℝ) {z : VoltageJetSpace μ U} (hz : z ∈ compactVoltageJets μ U) :
    c • z ∈ compactVoltageJets μ U := by
  obtain ⟨v,hv,hvc,hvs,hvm,hvg,rfl⟩ := hz
  have he := voltageGradient_smul c (hv.differentiable (by simp))
  have hmg : MemLp (voltageGradient (c • v)) 2 (μ.restrict U) := by
    rw [he]; exact hvg.const_smul c
  refine ⟨c • v,hv.const_smul c,hvc.smul_left,
    (tsupport_smul_subset_right (fun _ : Coord3 => c) v).trans hvs,
    hvm.const_smul c,hmg,?_⟩
  apply Prod.ext
  · exact (MemLp.toLp_const_smul c hvm).symm
  · change c • hvg.toLp _ = hmg.toLp _
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => congrFun he x |>.symm)

def compactVoltageJetModule (μ : Measure Coord3) (U : Set Coord3) :
    Submodule ℝ (VoltageJetSpace μ U) where
  carrier := compactVoltageJets μ U
  zero_mem' := compactVoltageJets_zero μ U
  add_mem' := compactVoltageJets_add μ U
  smul_mem' := compactVoltageJets_smul μ U

def zeroVoltageJets (μ : Measure Coord3) (U : Set Coord3) :
    Submodule ℝ (VoltageJetSpace μ U) :=
  (compactVoltageJetModule μ U).topologicalClosure

instance zeroVoltageJets_complete (μ : Measure Coord3) (U : Set Coord3) :
    CompleteSpace (zeroVoltageJets μ U) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

lemma zeroVoltageJets_poincare
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] {U : Set Coord3}
    (hUb : Bornology.IsBounded U) {z : VoltageJetSpace μ U} (hz : z ∈ zeroVoltageJets μ U) :
    ‖z.1‖ ≤ (eLpNormLESNormFDerivOfLeConst (Fin 2 → ℝ) μ U 2 2 *
      gradientCoordinateConstant : ℝ≥0) * ‖z.2‖ := by
  apply closure_minimal (s := compactVoltageJets μ U) ?_ ?_ hz
  · rintro _ ⟨v,hv,hvc,hvs,hvm,hvg,rfl⟩
    change ‖hvm.toLp _‖ ≤ _ * ‖hvg.toLp _‖
    rw [Lp.norm_toLp,Lp.norm_toLp]
    exact compact_voltage_poincare μ hUb hv hvc hvs
  · exact isClosed_le continuous_fst.norm (continuous_const.mul continuous_snd.norm)

def zeroVoltageGradientMap (μ : Measure Coord3) (U : Set Coord3) :
    zeroVoltageJets μ U →L[ℝ] Lp FieldVector 2 (μ.restrict U) :=
  (ContinuousLinearMap.snd ℝ _ _).comp (zeroVoltageJets μ U).subtypeL

lemma zeroVoltageGradientMap_closed_range
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] {U : Set Coord3}
    (hUb : Bornology.IsBounded U) : IsClosed (Set.range (zeroVoltageGradientMap μ U)) := by
  let C : ℝ≥0 := eLpNormLESNormFDerivOfLeConst (Fin 2 → ℝ) μ U 2 2 * gradientCoordinateConstant
  apply ((zeroVoltageGradientMap μ U).antilipschitz_of_bound (K := C+1) ?_).isClosed_range
    (zeroVoltageGradientMap μ U).uniformContinuous
  intro z
  change ‖z.val‖ ≤ ((C+1 : ℝ≥0) : ℝ) * ‖z.val.2‖
  rw [Prod.norm_def,max_le_iff]
  constructor
  · exact (zeroVoltageJets_poincare μ hUb z.property).trans
      (by change (C : ℝ) * _ ≤ _; push_cast; nlinarith [norm_nonneg z.val.2])
  · have hC : 0 ≤ (C : ℝ) := C.coe_nonneg
    push_cast
    nlinarith [norm_nonneg z.val.2]

end ScalarConductivity

end
end

end OAI
