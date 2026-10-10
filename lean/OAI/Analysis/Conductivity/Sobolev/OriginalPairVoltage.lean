import Mathlib
import OAI.Analysis.Conductivity.Sobolev.OriginalH1VoltageRestriction

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

def originalPairVoltageJet (U : Set Coord3) (w : Fin 2 → H1) : VoltageJetSpace volume U :=
  originalVoltageJetCLM U 0 (w 0).val + originalVoltageJetCLM U 1 (w 1).val

lemma originalPairVoltageJet_H1 {U : Set Coord3} (hU : MeasurableSet U)
    (hb : ∀ y∈U,WithLp.toLp 2 y∈ball) (hbounded : Bornology.IsBounded U) (w : Fin 2 → H1) :
    originalPairVoltageJet U w∈voltageH1Jets volume U :=
  (voltageH1Jets volume U).add_mem
    (originalVoltageJetCLM_H1 hU hb hbounded 0 (w 0))
    (originalVoltageJetCLM_H1 hU hb hbounded 1 (w 1))

lemma originalPairVoltageJet_ae {U : Set Coord3} (hU : MeasurableSet U)
    (hb : ∀ y∈U,WithLp.toLp 2 y∈ball) (w : Fin 2 → H1) :
    (originalPairVoltageJet U w).1=ᵐ[volume.restrict U]
      (fun y j => weakValue (w j) (WithLp.toLp 2 y)) ∧
    (originalPairVoltageJet U w).2=ᵐ[volume.restrict U]
      (fun y => WithLp.toLp 2 (fun ij => originalPiGradient (w ij.2) y ij.1)) := by
  have h0 := originalVoltageJetCLM_ae U hU hb 0 (w 0).val
  have h1 := originalVoltageJetCLM_ae U hU hb 1 (w 1).val
  constructor
  · filter_upwards [Lp.coeFn_add (originalVoltageJetCLM U 0 (w 0).val).1
      (originalVoltageJetCLM U 1 (w 1).val).1,h0.1,h1.1] with y he h0 h1
    change ((originalVoltageJetCLM U 0 (w 0).val).1+(originalVoltageJetCLM U 1 (w 1).val).1) y=_
    rw [he,Pi.add_apply,h0,h1]
    ext j
    fin_cases j <;> simp [weakValue,jetValue] <;> rfl
  · filter_upwards [Lp.coeFn_add (originalVoltageJetCLM U 0 (w 0).val).2
      (originalVoltageJetCLM U 1 (w 1).val).2,h0.2,h1.2] with y he h0 h1
    change ((originalVoltageJetCLM U 0 (w 0).val).2+(originalVoltageJetCLM U 1 (w 1).val).2) y=_
    rw [he,Pi.add_apply,h0,h1]
    ext ⟨i,j⟩
    fin_cases j <;> simp [originalPiGradient,weakGradient]

lemma voltageGradient_component {v : Coord3 → Fin 2 → ℝ} {y : Coord3}
    (hv : DifferentiableAt ℝ v y) (i : Fin 3) (j : Fin 2) :
    (voltageGradient v y) (i,j)=fderiv ℝ (fun x => v x j) y (Pi.single i 1) := by
  have he : fderiv ℝ (fun x => v x j) y=(ContinuousLinearMap.proj j).comp (fderiv ℝ v y) :=
    ((ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp y hv.hasFDerivAt).fderiv
  rw [he]
  rfl

theorem original_pair_voltageH1 {U : Set Coord3} (hU : MeasurableSet U)
    (hb : ∀ y∈U,WithLp.toLp 2 y∈ball) (hbounded : Bornology.IsBounded U)
    (w : Fin 2 → H1) (v : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (hv : ∀ᵐ y : Coord3,y∈U → v y=fun j => weakValue (w j) (WithLp.toLp 2 y))
    (hd : ∀ᵐ y : Coord3,y∈U → ∀ i : Fin 3,∀ j : Fin 2,
      fderiv ℝ (fun x => v x j) y (Pi.single i 1)=weakGradient (w j) (WithLp.toLp 2 y) i)
    (hr : volume (U \ regularRegion v A U)=0) :
    ∃ (hu : MemLp v 2 (volume.restrict U)) (hE : MemLp (voltageGradient v) 2 (volume.restrict U)),
      (hu.toLp _,hE.toLp _)=originalPairVoltageJet U w ∧
      (hu.toLp _,hE.toLp _)∈voltageH1Jets volume U := by
  have hp := originalPairVoltageJet_ae hU hb w
  have he : voltageGradient v=ᵐ[volume.restrict U]
      (fun y => WithLp.toLp 2 (fun ij => originalPiGradient (w ij.2) y ij.1)) := by
    filter_upwards [ae_restrict_of_ae hd,ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hr),
      ae_restrict_mem hU] with y hd hr hy
    have hyR : y∈regularRegion v A U := by simpa only [Set.mem_sdiff,hy,true_and,not_not] using hr
    ext ⟨i,j⟩
    rw [voltageGradient_component (regularRegion_differentiable hyR),hd hy i j]
    rfl
  have hv' : v=ᵐ[volume.restrict U] (originalPairVoltageJet U w).1 := by
    filter_upwards [ae_restrict_of_ae hv,ae_restrict_mem hU,hp.1] with y hv hy hp
    exact (hv hy).trans hp.symm
  have hg' := he.trans hp.2.symm
  let hu := (Lp.memLp (originalPairVoltageJet U w).1).ae_eq hv'.symm
  let hE := (Lp.memLp (originalPairVoltageJet U w).2).ae_eq hg'.symm
  have hh : (hu.toLp _,hE.toLp _)=originalPairVoltageJet U w := by
    apply Prod.ext
    · exact Lp.ext (hu.coeFn_toLp.trans hv')
    · exact Lp.ext (hE.coeFn_toLp.trans hg')
  exact ⟨hu,hE,hh,hh ▸ originalPairVoltageJet_H1 hU hb hbounded w⟩

end ScalarConductivity

end
end

end OAI
