import Mathlib
import OAI.Analysis.Conductivity.Sobolev.SobolevGaugeTransform
import OAI.Analysis.Conductivity.Walls.PhysicalTerminalCutoff
import OAI.Analysis.Conductivity.Sources.PhysicalPatching
import OAI.Analysis.Conductivity.Sources.PhysicalTrace

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
attribute [local instance] Classical.propDecidable
local instance physicalRootMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalRootIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

theorem source_patch_trace_exists
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {η : ℝ} (hη : 0<η) (hηc : 2*η<centralThickness)
    (hT : ∀ i : Fin 3,∀ t : ℝ,|t|≤η → (z.ending i).R<z.compression i*(t-terminalBase i))
    (w q : Fin 2 → H1) (he : ∀ j i,H1JetOn (w j) (physicalEndRegion i) (z.correctedEndJet j i))
    (Z : VoltageJetSpace volume physicalOpenBlock)
    (hZ : Z∈zeroVoltageJets volume physicalOpenBlock)
    (hq : ∀ j,(q j-w j).val=voltageOriginalJetCLM physicalOpenBlock_open.measurableSet j Z)
    (j : Fin 2) :
    ∃ W : H1,W∈H10 ∧ (∀ᵐ x∂ballMeasure,weakValue W x=
      if WithLp.ofLp x∈physicalOpenBlock then weakValue (q j) x-z.terminalValue 0 j
      else z.terminalProfile η j (WithLp.ofLp x)) ∧
      ∀ i : Fin 3,physicalRealTraceCLM i W=ᵐ[volume] fun _ => z.terminalValue i j-z.terminalValue 0 j := by
  obtain ⟨f,hf,hfv⟩ := z.terminalProfile_H10 hη hηc j
  obtain ⟨χ,hχ,hχc,hχs,hχ1⟩ := terminal_cutoff_exists hη
  let E : R3 ≃L[ℝ] Coord3 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hχd : ContDiff ℝ (↑(⊤:ℕ∞)) (χ ∘ E) := hχ.comp E.contDiff
  have hχcc : HasCompactSupport (χ ∘ E) := hχc.comp_homeomorph E.toHomeomorph
  have hχblock : tsupport (χ ∘ E)⊆E ⁻¹' physicalOpenBlock := by
    have hh : tsupport (χ ∘ E)⊆E ⁻¹' tsupport χ :=
      closure_minimal (fun y hy => subset_tsupport χ hy) ((isClosed_tsupport χ).preimage E.continuous)
    intro x hx
    exact hχs (hh hx)
  have hχss : tsupport (χ ∘ E)⊆ball := fun _ hx => physicalOpenBlock_subset_ball (hχblock hx)
  let u := w j-constantH1 (z.terminalValue 0 j)-f
  obtain ⟨v,hv,hvv⟩ := original_smooth_mul_exists hχd hχcc hχss u
  have hd : q j-w j∈H10 := by
    change (q j-w j).val∈zeroTraceAmbient
    rw [hq]
    exact voltageOriginalJetCLM_zeroTrace physicalOpenBlock_open.measurableSet
      (fun _ => physicalOpenBlock_subset_ball) j hZ
  have hband := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
    (z.terminal_band_value hs hη hηc hT w he j))
  have hdv : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∉physicalOpenBlock → weakValue (q j-w j) x=0 := by
    have hz := voltageOriginalJetCLM_ae physicalOpenBlock_open.measurableSet j Z
    rw [←hq j] at hz
    filter_upwards [hz] with x hx hxn
    have hh := congrArg (fun f : JetFiber => f 0) hx
    change (q j-w j).val x 0=0
    rw [hx,ite_eq_right hxn]
    rfl
  refine ⟨v+f+(q j-w j),H10.add_mem (H10.add_mem hv hf) hd,?_,?_⟩
  · filter_upwards [hvv,hfv,hband,hdv,weakValue_add (v+f) (q j-w j),weakValue_add v f,
      weakValue_sub (w j-constantH1 (z.terminalValue 0 j)) f,
      (H1_sub_constant_spec (w j) (z.terminalValue 0 j)).1,weakValue_sub (q j) (w j)]
      with x hmv hfv hband hdv hsum hadd hu1 hu2 hd1
    rw [hsum]
    simp only [Pi.add_apply]
    rw [hadd]
    simp only [Pi.add_apply]
    have hu : weakValue u x=weakValue (w j) x-z.terminalValue 0 j-z.terminalProfile η j (WithLp.ofLp x) := by
      change weakValue (w j-constantH1 (z.terminalValue 0 j)-f) x=_
      rw [hu1,Pi.sub_apply,hu2,hfv]
    rw [hmv,hu,hfv]
    change χ (WithLp.ofLp x)*(weakValue (w j) x-z.terminalValue 0 j-z.terminalProfile η j (WithLp.ofLp x))+
      z.terminalProfile η j (WithLp.ofLp x)+weakValue (q j-w j) x=_
    by_cases hx : WithLp.ofLp x∈physicalOpenBlock
    · rw [ite_eq_left hx,hd1]
      simp only [Pi.sub_apply]
      by_cases hc : WithLp.ofLp x∈terminalCore η
      · rw [hχ1 _ hc]; ring
      · have hh := hband hx hc
        simp only [WithLp.toLp_ofLp] at hh
        rw [show weakValue (w j) x-z.terminalValue 0 j-z.terminalProfile η j (WithLp.ofLp x)=0 by linarith]
        linarith
    · rw [ite_eq_right hx,hdv hx]
      have hz : χ (WithLp.ofLp x)=0 := image_eq_zero_of_notMem_tsupport (fun hn => hx (hχs hn))
      rw [hz]
      ring
  · intro i
    have htv := physicalOuterTrace_compact_mul hχd hχcc hχblock u v hvv i
    have htd := voltageOriginal_outer_trace_zero j hZ (q j-w j) (hq j) i
    have hrzero (u : H1) (hu : physicalOuterTraceCLM i u=0) : physicalRealTraceCLM i u=0 := by
      change Complex.reCLM.compLpL 2 volume ((mFourierBasis (d:=Fin 2)).repr.symm (physicalOuterTraceCLM i u))=0
      rw [hu,map_zero,map_zero]
    rw [map_add,map_add,hrzero v htv,hrzero (q j-w j) htd,zero_add,add_zero]
    exact z.terminalProfile_trace hη hηc j f hfv i

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

end OAI
