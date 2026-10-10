import Mathlib
import OAI.Analysis.Conductivity.Sobolev.VoltageJetCompletion
import OAI.Analysis.Conductivity.Variational.CompactBridge
import OAI.Analysis.Conductivity.Variational.WholeBallJet

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal Classical

def voltageValueComponentJet (j : Fin 2) : (Fin 2 → ℝ) →L[ℝ] JetFiber :=
  ({ toFun := fun v => WithLp.toLp 2 (Fin.cases (v j) (fun _ => 0))
     map_add' := by intro v w; ext i; refine Fin.cases ?_ (fun k => ?_) i <;> simp
     map_smul' := by intro c v; ext i; refine Fin.cases ?_ (fun k => ?_) i <;> simp } :
    (Fin 2 → ℝ) →ₗ[ℝ] JetFiber).toContinuousLinearMap

def voltageGradientComponentJet (j : Fin 2) : FieldVector →L[ℝ] JetFiber :=
  ({ toFun := fun v => WithLp.toLp 2 (Fin.cases 0 (fun i => v (i,j)))
     map_add' := by intro v w; ext i; refine Fin.cases ?_ (fun k => ?_) i <;> simp
     map_smul' := by intro c v; ext i; refine Fin.cases ?_ (fun k => ?_) i <;> simp } :
    FieldVector →ₗ[ℝ] JetFiber).toContinuousLinearMap

def voltageComponentJetCLM (μ : Measure Coord3) (U : Set Coord3) (j : Fin 2) :
    VoltageJetSpace μ U →L[ℝ] Lp JetFiber 2 (μ.restrict U) :=
  ((voltageValueComponentJet j).compLpL 2 (μ.restrict U)).comp
    (ContinuousLinearMap.fst ℝ _ _)+
  ((voltageGradientComponentJet j).compLpL 2 (μ.restrict U)).comp
    (ContinuousLinearMap.snd ℝ _ _)

lemma voltageComponentJetCLM_ae (μ : Measure Coord3) (U : Set Coord3) (j : Fin 2)
    (z : VoltageJetSpace μ U) :
    voltageComponentJetCLM μ U j z=ᵐ[μ.restrict U]
      fun x => WithLp.toLp 2 (Fin.cases (z.1 x j) (fun i => z.2 x (i,j))) := by
  have h1 := (voltageValueComponentJet j).coeFn_compLpL (p:=2) (μ:=μ.restrict U) z.1
  have h2 := (voltageGradientComponentJet j).coeFn_compLpL (p:=2) (μ:=μ.restrict U) z.2
  have ha := Lp.coeFn_add ((voltageValueComponentJet j).compLpL 2 (μ.restrict U) z.1)
    ((voltageGradientComponentJet j).compLpL 2 (μ.restrict U) z.2)
  filter_upwards [h1,h2,ha] with x h1 h2 ha
  change (((voltageValueComponentJet j).compLpL 2 (μ.restrict U) z.1)+
    ((voltageGradientComponentJet j).compLpL 2 (μ.restrict U) z.2)) x=_
  rw [ha,Pi.add_apply,h1,h2]
  ext i
  refine Fin.cases ?_ (fun k => ?_) i <;>
    simp [voltageValueComponentJet,voltageGradientComponentJet]

def voltageOriginalJetCLM {U : Set Coord3} (hU : MeasurableSet U) (j : Fin 2) :
    VoltageJetSpace volume U →L[ℝ] JetSpace :=
  (lpRestrictionCLM ball).comp
    (((Lp.compMeasurePreservingₗᵢ ℝ
      (WithLp.ofLp : R3 → Coord3)
      (PiLp.volume_preserving_ofLp (Fin 3))).toContinuousLinearMap).comp
      ((lpZeroExtensionCLM hU).comp (voltageComponentJetCLM volume U j)))

lemma voltageOriginalJetCLM_ae {U : Set Coord3} (hU : MeasurableSet U) (j : Fin 2)
    (z : VoltageJetSpace volume U) :
    voltageOriginalJetCLM hU j z=ᵐ[ballMeasure] fun x =>
      if WithLp.ofLp x∈U then WithLp.toLp 2
        (Fin.cases (z.1 (WithLp.ofLp x) j) (fun i => z.2 (WithLp.ofLp x) (i,j))) else 0 := by
  have he := lpZeroExtensionCLM_ae_of_ae hU
    (voltageComponentJetCLM volume U j z) (voltageComponentJetCLM_ae volume U j z)
  have hp := (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp he
  have hc := Lp.coeFn_compMeasurePreserving
    (lpZeroExtensionCLM hU (voltageComponentJetCLM volume U j z))
    (PiLp.volume_preserving_ofLp (Fin 3))
  have hr := lpRestrictionCLM_ae ball
    ((Lp.compMeasurePreservingₗᵢ ℝ
      (WithLp.ofLp : R3 → Coord3)
      (PiLp.volume_preserving_ofLp (Fin 3)))
      (lpZeroExtensionCLM hU (voltageComponentJetCLM volume U j z)))
  apply hr.trans
  apply ae_restrict_of_ae
  filter_upwards [hc,hp] with x hc hp
  apply hc.trans
  rw [hp]
  by_cases hx : WithLp.ofLp x∈U <;> simp [hx]

lemma voltage_component_smoothJet {v : Coord3 → Fin 2 → ℝ}
    (hv : Differentiable ℝ v) (j : Fin 2) (x : R3) :
    smoothJet (fun x : R3 => v (WithLp.ofLp x) j) x=
      WithLp.toLp 2 (Fin.cases (v (WithLp.ofLp x) j)
        (fun i => voltageGradient v (WithLp.ofLp x) (i,j))) := by
  ext k
  refine Fin.cases rfl (fun i => ?_) k
  change gradient (fun x : R3 => v (WithLp.ofLp x) j) x i=_
  have herr : gradient (fun x : R3 => v (WithLp.ofLp x) j) x i=
      fderiv ℝ (fun x : R3 => v (WithLp.ofLp x) j) x (EuclideanSpace.single i 1) := by
    have h : inner ℝ (EuclideanSpace.single i 1)
        (gradient (fun x : R3 => v (WithLp.ofLp x) j) x)=
        fderiv ℝ (fun x : R3 => v (WithLp.ofLp x) j) x (EuclideanSpace.single i 1) := by
      simp only [inner_gradient_right,RCLike.conj_to_real]
    simpa only [EuclideanSpace.inner_single_left,RCLike.conj_to_real,one_mul] using h
  rw [herr]
  let P : R3 ≃L[ℝ] Coord3 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hd := ((ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp (P x)
    (hv (P x)).hasFDerivAt).comp x P.hasFDerivAt
  have hP : (P : R3 → Coord3)=WithLp.ofLp := rfl
  rw [show fderiv ℝ (fun x : R3 => v (WithLp.ofLp x) j) x=
    (ContinuousLinearMap.proj j).comp ((fderiv ℝ v (P x)).comp P.toContinuousLinearMap) from by
      simpa only [Function.comp_def,ContinuousLinearMap.comp_assoc,ContinuousLinearMap.proj_apply,hP] using hd.fderiv]
  rfl

lemma voltageOriginalJetCLM_compact {U : Set Coord3} (hU : MeasurableSet U)
    (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball) (j : Fin 2)
    {z : VoltageJetSpace volume U} (hz : z∈compactVoltageJets volume U) :
    voltageOriginalJetCLM hU j z∈zeroTraceAmbient := by
  obtain ⟨v,hv,hvc,hvs,hm,hg,rfl⟩ := hz
  let P : R3 ≃L[ℝ] Coord3 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hP : (P : R3 → Coord3)=WithLp.ofLp := rfl
  let f : R3 → ℝ := fun x => v (WithLp.ofLp x) j
  have hf : ContDiff ℝ (↑(⊤:ℕ∞)) f := by
    simpa only [Function.comp_def,hP] using
      (((contDiff_apply ℝ ℝ j).comp hv).comp P.contDiff)
  have hfc : HasCompactSupport f := by
    simpa only [Function.comp_def,show (P.toHomeomorph : R3 → Coord3)=WithLp.ofLp from rfl] using
      (hvc.comp_left (g:=fun w : Fin 2 → ℝ => w j) rfl).comp_homeomorph P.toHomeomorph
  have hfsU : tsupport f⊆(WithLp.ofLp : R3 → Coord3)⁻¹' U := by
    intro x hx
    have hs := tsupport_comp_subset_preimage (fun y : Coord3 => v y j) P.continuous
    have hm : P x∈tsupport (fun y : Coord3 => v y j) := hs hx
    exact hvs ((tsupport_comp_subset (g:=fun w : Fin 2 → ℝ => w j) rfl v) hm)
  have hfs : tsupport f⊆ball := by
    intro x hx
    simpa only [WithLp.toLp_ofLp] using hUb (WithLp.ofLp x) (hfsU hx)
  have hm' := (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' hU).1 hm.coeFn_toLp)
  have hg' := (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' hU).1 hg.coeFn_toLp)
  have he : voltageOriginalJetCLM hU j (hm.toLp _,hg.toLp _)=(smoothH1 f hf).val := by
    apply Lp.ext
    filter_upwards [voltageOriginalJetCLM_ae hU j (hm.toLp _,hg.toLp _),
      ae_restrict_of_ae hm',ae_restrict_of_ae hg',(smoothJet_memLp hf).coeFn_toLp]
      with x hx hm hg hfx
    change _=(smoothJet_memLp hf).toLp _ x
    rw [hfx,hx]
    by_cases hu : WithLp.ofLp x∈U
    · rw [ite_eq_left hu,hm hu,hg hu]
      exact (voltage_component_smoothJet (hv.differentiable (by simp)) j x).symm
    · rw [ite_eq_right hu]
      exact (smoothJet_zero_of_notMem_support (fun hh => hu (hfsU hh))).symm
  rw [he]
  exact smoothH1_mem_H10 f hf hfc hfs

theorem voltageOriginalJetCLM_zeroTrace {U : Set Coord3} (hU : MeasurableSet U)
    (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball) (j : Fin 2)
    {z : VoltageJetSpace volume U} (hz : z∈zeroVoltageJets volume U) :
    voltageOriginalJetCLM hU j z∈zeroTraceAmbient := by
  exact closure_minimal
    (fun z hz => voltageOriginalJetCLM_compact hU hUb j hz)
    ((Submodule.isClosed_topologicalClosure _).preimage
      (voltageOriginalJetCLM hU j).continuous) hz

theorem voltage_original_H10_extension {U : Set Coord3} (hU : MeasurableSet U)
    (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball) (j : Fin 2)
    {z : VoltageJetSpace volume U} (hz : z∈zeroVoltageJets volume U) :
    ∃ w : H1,w∈H10 ∧ w.val=voltageOriginalJetCLM hU j z ∧
      ∀ᵐ x∂ballMeasure,
        weakValue w x=(if WithLp.ofLp x∈U then z.1 (WithLp.ofLp x) j else 0) ∧
        ∀ i,weakGradient w x i=(if WithLp.ofLp x∈U then z.2 (WithLp.ofLp x) (i,j) else 0) := by
  have hzero := voltageOriginalJetCLM_zeroTrace hU hUb j hz
  let w : H1 := ⟨voltageOriginalJetCLM hU j z,zeroTraceAmbient_le_H1Space hzero⟩
  refine ⟨w,hzero,rfl,?_⟩
  filter_upwards [voltageOriginalJetCLM_ae hU j z] with x hx
  change w.val x=_ at hx
  by_cases hm : WithLp.ofLp x∈U
  · rw [ite_eq_left hm] at hx
    constructor
    · change w.val x 0=_
      rw [hx,ite_eq_left hm]
      rfl
    · intro i
      change (w.val x) i.succ=_
      rw [hx,ite_eq_left hm]
      rfl
  · rw [ite_eq_right hm] at hx
    constructor
    · change w.val x 0=_
      rw [hx,ite_eq_right hm]
      rfl
    · intro i
      change (w.val x) i.succ=_
      rw [hx,ite_eq_right hm]
      rfl

end ScalarConductivity

end
end

end OAI
