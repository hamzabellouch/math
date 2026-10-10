import Mathlib
import OAI.Analysis.Commutator.PointwiseLinearLift
import OAI.Analysis.Commutator.ScalarIndicator

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma operator_commutes_indicator (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (s : Set Ω) (hs : MeasurableSet s) :
    Commute (operator μ T hm hb) (indicatorOperator μ s hs) := by
  classical
  change operator μ T hm hb*indicatorOperator μ s hs=
    indicatorOperator μ s hs*operator μ T hm hb
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [operator_ae μ T hm hb (indicatorOperator μ s hs f),
    indicatorOperator_ae μ s hs f,indicatorOperator_ae μ s hs (operator μ T hm hb f),
    operator_ae μ T hm hb f] with a ha hi hi' ha'
  change operator μ T hm hb (indicatorOperator μ s hs f) a=
    indicatorOperator μ s hs (operator μ T hm hb f) a
  rw [ha,hi,hi']
  by_cases hx : a∈s
  · simp only [Set.indicator_of_mem hx,ha']
  · simp [hx]

variable [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

theorem exists_field_of_commutes_indicator (Y : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hcomm : ∀ (s : Set Ω) (hs : MeasurableSet s),Commute Y (indicatorOperator μ s hs)) :
    ∃ (T : Ω → H →L[ℂ] H) (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
      (hb : ∀ᵐ a ∂μ,‖T a‖≤‖Y‖),Y=operator μ T hm hb := by
  let A := Y.comp (Lp.constL 2 μ ℂ)
  have hA : ∀ ξ : H,∀ᵐ a ∂μ,‖A ξ a‖≤‖Y‖*‖ξ‖ := fun ξ =>
    local_constant_ae_bound μ Y hcomm ξ
  let T := PointwiseLift.field μ A ‖Y‖
  have hm := PointwiseLift.field_measurable μ A ‖Y‖ (norm_nonneg Y) hA
  have hb : ∀ᵐ a ∂μ,‖T a‖≤‖Y‖ := Eventually.of_forall
    (PointwiseLift.field_norm_le μ A ‖Y‖ (norm_nonneg Y))
  let M := operator μ T hm hb
  have he (ξ : H) : M (Lp.const 2 μ ξ)=Y (Lp.const 2 μ ξ) := by
    apply Lp.ext
    filter_upwards [operator_ae μ T hm hb (Lp.const 2 μ ξ),
      Lp.coeFn_const (p:=2) (μ:=μ) (c:=ξ),
      PointwiseLift.field_ae μ A ‖Y‖ (norm_nonneg Y) hA ξ] with a ha hc hf
    change M (Lp.const 2 μ ξ) a=T a ((Lp.const 2 μ ξ) a) at ha
    change T a ξ=Y (Lp.const 2 μ ξ) a at hf
    rw [ha,hc]
    exact hf
  have hM : M=Y := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.induction (by norm_num : (2:ENNReal)≠⊤) (fun f => M f=Y f)
    · intro ξ s hs hμs
      rw [Lp.simpleFunc.coe_indicatorConst,←indicatorOperator_const μ s hs ξ]
      calc
        M (indicatorOperator μ s hs (Lp.const 2 μ ξ))=
            indicatorOperator μ s hs (M (Lp.const 2 μ ξ)) :=
          congrArg (fun B : Lp H 2 μ →L[ℂ] Lp H 2 μ => B (Lp.const 2 μ ξ))
            (operator_commutes_indicator μ T hm hb s hs).eq
        _=indicatorOperator μ s hs (Y (Lp.const 2 μ ξ)) := by rw [he]
        _=Y (indicatorOperator μ s hs (Lp.const 2 μ ξ)) :=
          congrArg (fun B : Lp H 2 μ →L[ℂ] Lp H 2 μ => B (Lp.const 2 μ ξ)) (hcomm s hs).eq.symm
    · intro f g hf hg hd hMf hMg
      simp only [map_add,hMf,hMg]
    · exact isClosed_eq M.continuous Y.continuous
  exact ⟨T,hm,hb,hM.symm⟩

end Kadison.Decomposable

end

end
end

end OAI
