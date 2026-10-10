import Mathlib
import OAI.Analysis.Conductivity.Sobolev.OriginalH1VoltageRestriction

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal Classical

lemma originalVoltageJetCLM_pairing {U : Set Coord3} (hU : MeasurableSet U)
    (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball) (u : H1) (j : Fin 2)
    (F : Lp FieldVector 2 (volume.restrict U)) :
    inner ℝ (originalVoltageJetCLM U j u.val).2 F=
      ∫ x,∑ i,weakGradient u (WithLp.toLp 2 x) i*F x (i,j) ∂volume.restrict U := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(originalVoltageJetCLM_ae U hU hUb j u.val).2] with x hx
  rw [hx]
  simp [PiLp.inner_apply,RCLike.inner_apply,Fintype.sum_prod_type,weakGradient,mul_comm]

theorem scalarization_original_weak_gradient_cauchy {U : Set Coord3} (hU : MeasurableSet U)
    (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball) (hbounded : Bornology.IsBounded U)
    {F G : Lp FieldVector 2 (volume.restrict U)}
    (hF : ∀ W : voltageH1Jets volume U,inner ℝ W.val.2 F=inner ℝ W.val.2 G)
    (u : H1) (j : Fin 2) :
    (∫ x,∑ i,weakGradient u (WithLp.toLp 2 x) i*F x (i,j) ∂volume.restrict U)=
      (∫ x,∑ i,weakGradient u (WithLp.toLp 2 x) i*G x (i,j) ∂volume.restrict U) := by
  rw [←originalVoltageJetCLM_pairing hU hUb u j F,←originalVoltageJetCLM_pairing hU hUb u j G]
  exact scalarization_original_H1_test_bridge hU hUb hbounded hF u j

end ScalarConductivity

end
end

end OAI
