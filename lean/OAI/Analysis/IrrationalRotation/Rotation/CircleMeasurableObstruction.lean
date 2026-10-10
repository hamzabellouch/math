import OAI.Analysis.IrrationalRotation.Couplings.CircleConditionalConvolutionData
import OAI.Analysis.IrrationalRotation.Operators.ProjectionTruncationMass

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Invariant233.CircleParameterLaws
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)

theorem measurableOperator_hasOnlyTrivialInvariantProjections (hθ : Irrational θ) :
    HasOnlyTrivialInvariantProjections (Rotation.algebra θ) (p.measurableOperator θ hp) := by
  intro P hPm hP hT
  by_cases hP0 : P = 0
  · exact Or.inl hP0
  by_cases hP1 : P = 1
  · exact Or.inr hP1
  exfalso
  let hr := MixedRadix.radices_pos hp.q_pos hp.frequency_increasing hp.frequency_divisible
  obtain ⟨F, hF, _hbound, hFm, hrep, _hgraph, J, hJpos, hmass⟩ :=
    hp.exists_rational_graph_field_with_truncation_mass hθ hr hPm hP hT hP0 hP1
  have hc : (0 : ℝ) < Real.exp (-90) / 2 := by positivity
  have hsmall : ∀ᶠ j : ℕ in atTop, 1 / (j : ℝ) < Real.exp (-90) / 2 :=
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hc)
  obtain ⟨j, hjJ, hjc⟩ := ((eventually_ge_atTop J).and hsmall).exists
  have hj : 1 ≤ j := hJpos.trans hjJ
  have hm : Real.exp (-90) / 2 ≤ (CircleCoupling.law p j).real
      (CircleCoupling.truncationEvent p j hr
        (fun z => ((F z ProjectionCocycleWindow.basisZero) 0).re)) := by
    simpa only [PositiveDiagonalModel.e0, ProjectionCocycleWindow.basisZero,
      lp.inner_single_left, RCLike.inner_apply, star_one, map_one, one_mul, mul_one] using hmass j hjJ
  let := CircleCoupling.law_isProbabilityMeasure hp j
  exact hp.no_conditional_data_at_stage j hj (Real.exp (-90) / 2) hjc
    (CircleCoupling.conditionalData_of_truncation_mass hp j hj hr hPm hP hT
      F hF hFm hrep (Real.exp (-90) / 2) hm)

end Invariant233.CircleParameterLaws

end

end OAI
