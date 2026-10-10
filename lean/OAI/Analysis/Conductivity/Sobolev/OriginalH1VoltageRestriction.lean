import Mathlib
import OAI.Analysis.Conductivity.Variational.C1VoltageApproximation
import OAI.Analysis.Conductivity.Variational.OriginalVoltageRestriction

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal Classical

lemma original_voltage_potential_smooth (f : R3 → ℝ)
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (j : Fin 2) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun y : Coord3 => fun k : Fin 2 => if k=j then f (WithLp.toLp 2 y) else 0) := by
  let P : Coord3 ≃L[ℝ] R3 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  apply contDiff_pi.mpr
  intro k
  by_cases hk : k=j
  · simpa only [hk,ite_true,Function.comp_def,show (P : Coord3 → R3)=WithLp.toLp 2 from rfl]
      using hf.comp P.contDiff
  · simpa only [hk,ite_false] using
      (contDiff_const : ContDiff ℝ (↑(⊤:ℕ∞)) (fun _ : Coord3 => (0:ℝ)))

lemma originalVoltageJetCLM_smooth {U : Set Coord3} (hU : MeasurableSet U)
    (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball) (hbounded : Bornology.IsBounded U)
    (j : Fin 2) {z : JetSpace} (hz : z∈smoothJets) :
    originalVoltageJetCLM U j z∈smoothVoltageJets volume U := by
  obtain ⟨f,hf,hm,rfl⟩ := hz
  let v : Coord3 → Fin 2 → ℝ := fun y k => if k=j then f (WithLp.toLp 2 y) else 0
  have hv := original_voltage_potential_smooth f hf j
  obtain ⟨hu,hg,hh⟩ := C1_voltageJet_mem (hv.of_le (by simp)) hbounded hU
  refine ⟨v,hv,hu,hg,?_⟩
  have hm' := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' (show MeasurableSet ball from Metric.isOpen_ball.measurableSet)).1 hm.coeFn_toLp)
  have hae := originalVoltageJetCLM_ae U hU hUb j (hm.toLp _)
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [hae.1,ae_restrict_of_ae hm',ae_restrict_mem hU,hu.coeFn_toLp]
      with x hx hm hxU hu
    rw [hx,hu]
    funext k
    rw [hm (hUb x hxU)]
    rfl
  · apply Lp.ext
    filter_upwards [hae.2,ae_restrict_of_ae hm',ae_restrict_mem hU,hg.coeFn_toLp]
      with x hx hm hxU hg
    rw [hx,hg]
    have he := original_voltage_smooth_gradient f hf j x
    rw [he]
    congr 1
    funext ik
    rw [hm (hUb x hxU)]

theorem originalVoltageJetCLM_H1 {U : Set Coord3} (hU : MeasurableSet U)
    (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball) (hbounded : Bornology.IsBounded U)
    (j : Fin 2) (u : H1) :
    originalVoltageJetCLM U j u.val∈voltageH1Jets volume U := by
  have hs : H1Space ≤ (voltageH1Jets volume U).comap (originalVoltageJetCLM U j).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      intro z hz
      exact (Submodule.span ℝ (smoothVoltageJets volume U)).le_topologicalClosure
        (Submodule.subset_span (originalVoltageJetCLM_smooth hU hUb hbounded j hz))
    · exact (Submodule.isClosed_topologicalClosure _).preimage (originalVoltageJetCLM U j).continuous
  exact hs u.property

theorem scalarization_original_H1_test_bridge {U : Set Coord3} (hU : MeasurableSet U)
    (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball) (hbounded : Bornology.IsBounded U)
    {F G : Lp FieldVector 2 (volume.restrict U)}
    (hF : ∀ W : voltageH1Jets volume U,inner ℝ W.val.2 F=inner ℝ W.val.2 G)
    (u : H1) (j : Fin 2) :
    inner ℝ (originalVoltageJetCLM U j u.val).2 F=
      inner ℝ (originalVoltageJetCLM U j u.val).2 G := by
  exact hF ⟨originalVoltageJetCLM U j u.val,originalVoltageJetCLM_H1 hU hUb hbounded j u⟩

end ScalarConductivity

end
end

end OAI
