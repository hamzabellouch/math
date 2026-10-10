import Mathlib
import OAI.Analysis.Conductivity.Sobolev.VoltageOriginalH10

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal Classical

def originalVoltageValue (j : Fin 2) : JetFiber →L[ℝ] (Fin 2 → ℝ) :=
  ({ toFun := fun w k => if k=j then w 0 else 0
     map_add' := by intro w v; ext k; by_cases h : k=j <;> simp [h]
     map_smul' := by intro c w; ext k; by_cases h : k=j <;> simp [h] } :
    JetFiber →ₗ[ℝ] (Fin 2 → ℝ)).toContinuousLinearMap

def originalVoltageGradient (j : Fin 2) : JetFiber →L[ℝ] FieldVector :=
  ({ toFun := fun w => WithLp.toLp 2 (fun ik => if ik.2=j then w ik.1.succ else 0)
     map_add' := by intro w v; ext k; by_cases h : k.2=j <;> simp [h]
     map_smul' := by intro c w; ext k; by_cases h : k.2=j <;> simp [h] } :
    JetFiber →ₗ[ℝ] FieldVector).toContinuousLinearMap

def originalCartesianJetCLM (U : Set Coord3) : JetSpace →L[ℝ] Lp JetFiber 2 (volume.restrict U) :=
  (lpRestrictionCLM U).comp
    (((Lp.compMeasurePreservingₗᵢ ℝ (WithLp.toLp 2 : Coord3 → R3)
      (PiLp.volume_preserving_toLp (Fin 3))).toContinuousLinearMap).comp
      (lpZeroExtensionCLM Metric.isOpen_ball.measurableSet))

def originalVoltageJetCLM (U : Set Coord3) (j : Fin 2) :
    JetSpace →L[ℝ] VoltageJetSpace volume U :=
  (((originalVoltageValue j).compLpL 2 (volume.restrict U)).prod
    ((originalVoltageGradient j).compLpL 2 (volume.restrict U))).comp
      (originalCartesianJetCLM U)

lemma originalCartesianJetCLM_ae (U : Set Coord3) (hU : MeasurableSet U)
    (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball) (z : JetSpace) :
    originalCartesianJetCLM U z=ᵐ[volume.restrict U]
      fun x => z (WithLp.toLp 2 x) := by
  have he := lpZeroExtensionCLM_ae (show MeasurableSet ball from Metric.isOpen_ball.measurableSet) z
  have hp := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp he
  have hc := Lp.coeFn_compMeasurePreserving
    (lpZeroExtensionCLM (show MeasurableSet ball from Metric.isOpen_ball.measurableSet) z)
    (PiLp.volume_preserving_toLp (Fin 3))
  have hr := lpRestrictionCLM_ae U
    ((Lp.compMeasurePreservingₗᵢ ℝ (WithLp.toLp 2 : Coord3 → R3)
      (PiLp.volume_preserving_toLp (Fin 3)))
      (lpZeroExtensionCLM (show MeasurableSet ball from Metric.isOpen_ball.measurableSet) z))
  apply hr.trans
  filter_upwards [ae_restrict_of_ae hc,ae_restrict_of_ae hp,ae_restrict_mem hU] with x hc hp hx
  apply hc.trans
  rw [hp]
  exact ite_eq_left (hUb x hx)

lemma originalVoltageJetCLM_ae (U : Set Coord3) (hU : MeasurableSet U)
    (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball) (j : Fin 2) (z : JetSpace) :
    (originalVoltageJetCLM U j z).1=ᵐ[volume.restrict U]
        (fun x k => if k=j then z (WithLp.toLp 2 x) 0 else 0) ∧
    (originalVoltageJetCLM U j z).2=ᵐ[volume.restrict U]
        (fun x => WithLp.toLp 2 (fun ik => if ik.2=j then z (WithLp.toLp 2 x) ik.1.succ else 0)) := by
  constructor
  · have hc := (originalVoltageValue j).coeFn_compLpL (originalCartesianJetCLM U z)
    filter_upwards [hc,originalCartesianJetCLM_ae U hU hUb z] with x hx hz
    change ((originalVoltageValue j).compLpL 2 (volume.restrict U) (originalCartesianJetCLM U z)) x=_
    rw [hx,hz]
    rfl
  · have hc := (originalVoltageGradient j).coeFn_compLpL (originalCartesianJetCLM U z)
    filter_upwards [hc,originalCartesianJetCLM_ae U hU hUb z] with x hx hz
    change ((originalVoltageGradient j).compLpL 2 (volume.restrict U) (originalCartesianJetCLM U z)) x=_
    rw [hx,hz]
    rfl

lemma original_voltage_smooth_gradient (f : R3 → ℝ)
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (j : Fin 2) (x : Coord3) :
    voltageGradient (fun y : Coord3 => fun k : Fin 2 => if k=j then f (WithLp.toLp 2 y) else 0) x=
      WithLp.toLp 2 (fun ik => if ik.2=j then (smoothJet f (WithLp.toLp 2 x)) ik.1.succ else 0) := by
  let v : Coord3 → Fin 2 → ℝ := fun y k => if k=j then f (WithLp.toLp 2 y) else 0
  let P : Coord3 ≃L[ℝ] R3 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hv : ContDiff ℝ (↑(⊤:ℕ∞)) v := by
    apply contDiff_pi.mpr
    intro k
    by_cases hk : k=j
    · simpa only [v,hk,ite_true,Function.comp_def,show (P : Coord3 → R3)=WithLp.toLp 2 from rfl] using hf.comp P.contDiff
    · simpa only [v,hk,ite_false] using (contDiff_const : ContDiff ℝ (↑(⊤:ℕ∞)) (fun _ : Coord3 => (0:ℝ)))
  ext ik
  have hg := congrArg (fun w : JetFiber => w ik.1.succ)
    (voltage_component_smoothJet (hv.differentiable (by simp)) ik.2 (WithLp.toLp 2 x))
  change (voltageGradient v x).ofLp (ik.1,ik.2)=_
  by_cases hk : ik.2=j
  · have hh : (fun y : R3 => v (WithLp.ofLp y) ik.2)=f := by
      funext y
      simp [v,hk]
    rw [hh] at hg
    simpa only [WithLp.ofLp_toLp,Fin.cases_succ,WithLp.ofLp_toLp,hk,ite_true] using hg.symm
  · have hh : (fun y : R3 => v (WithLp.ofLp y) ik.2)=(fun _ => (0:ℝ)) := by
      funext y
      simp [v,hk]
    rw [hh] at hg
    simpa [smoothJet,gradient_const,hk] using hg.symm

end ScalarConductivity

end
end

end OAI
