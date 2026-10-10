import Mathlib
import OAI.Analysis.Commutator.CyclicSpectralUnitary
import OAI.Analysis.Commutator.L2InfiniteSumCoordinates
import OAI.Analysis.Commutator.ScalarIndicator

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

open InfiniteAmplification

variable {Ω H ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [Countable ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [Countable ι] [CompleteSpace H] in
lemma evalL_indicator (i : ι) (s : Set Ω) (hs : MeasurableSet s) (v : Lp (Space ι H) 2 μ) :
    evalL μ i (indicatorOperator μ s hs v)=indicatorOperator μ s hs (evalL μ i v) := by
  classical
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLp (lp.evalCLM ℂ (fun _ : ι => H) 2 i)
    (indicatorOperator μ s hs v),indicatorOperator_ae μ s hs v,
    indicatorOperator_ae μ s hs (evalL μ i v),
    ContinuousLinearMap.coeFn_compLp (lp.evalCLM ℂ (fun _ : ι => H) 2 i) v] with x h₁ h₂ h₃ h₄
  change ((lp.evalCLM ℂ (fun _ : ι => H) 2 i).compLp (indicatorOperator μ s hs v)) x=_
  rw [h₁,h₃]
  change (indicatorOperator μ s hs v) x i=s.indicator (evalL μ i v) x
  rw [h₂]
  by_cases hx : x∈s
  · simp only [Set.indicator_of_mem hx]
    exact h₄.symm
  · simp [hx]

variable [TopologicalSpace Ω] [T2Space Ω] [CompactSpace Ω] [BorelSpace Ω]

omit [T2Space Ω] in
lemma vector_indicator_of_scalar (f : C(Ω,ℂ)) (s : Set Ω) (hs : MeasurableSet s)
    (hf : CyclicSpectral.scalarMultiplier μ f=indicatorOperator μ s hs) :
    scalarVectorMultiplier (H:=Space ι ℂ) μ f=indicatorOperator μ s hs := by
  apply ContinuousLinearMap.ext
  intro v
  apply sub_eq_zero.mp
  apply evalL_separates μ
  intro i
  rw [map_sub,evalL_scalarMultiplier,evalL_indicator]
  change (CyclicSpectral.scalarMultiplier μ f) (evalL μ i v)-indicatorOperator μ s hs (evalL μ i v)=0
  rw [hf,sub_self]

omit [T2Space Ω] in
lemma scalarVectorMultiplier_commutes_constant (f : C(Ω,ℂ)) (C : H →L[ℂ] H) :
    Commute (operator μ (fun _ => C) (fun _ => aestronglyMeasurable_const)
      (Eventually.of_forall (fun _ => le_rfl))) (scalarVectorMultiplier μ f) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [operator_ae μ (fun _ => C) (fun _ => aestronglyMeasurable_const)
    (Eventually.of_forall (fun _ => le_rfl)) (scalarVectorMultiplier μ f v),
    scalarVectorMultiplier_ae μ f v,
    scalarVectorMultiplier_ae μ f (operator μ (fun _ => C) (fun _ => aestronglyMeasurable_const)
      (Eventually.of_forall (fun _ => le_rfl)) v),
    operator_ae μ (fun _ => C) (fun _ => aestronglyMeasurable_const)
      (Eventually.of_forall (fun _ => le_rfl)) v] with x h₁ h₂ h₃ h₄
  change operator μ (fun _ => C) (fun _ => aestronglyMeasurable_const)
    (Eventually.of_forall (fun _ => le_rfl)) (scalarVectorMultiplier μ f v) x=
    scalarVectorMultiplier μ f (operator μ (fun _ => C) (fun _ => aestronglyMeasurable_const)
    (Eventually.of_forall (fun _ => le_rfl)) v) x
  rw [h₁,h₂,h₃,h₄]
  exact C.map_smul _ _

end Kadison.Decomposable

end

end
end

end OAI
