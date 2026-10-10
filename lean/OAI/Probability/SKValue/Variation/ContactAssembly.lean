import Mathlib
import OAI.Probability.SKValue.Processes.FiniteGaussianFixedStrip
import OAI.Probability.SKValue.Evolution.IntegralPrimitiveTerminal
import OAI.Probability.SKValue.Processes.GradientSquareIntegral
import OAI.Probability.SKValue.GroundState.WeakGuerra

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma normalizer_pos_iff (W : BrownianSpace) (γ : OrderParameter) (T : ℝ) (N j : ℕ) :
    0<normalizer W γ T N j ↔
    0<∫ z,(rawCoefficient W γ T N j z)^2 ∂gaussianProduct (Fin (N+1)) := by
  unfold normalizer
  rw [inv_pos, Real.sqrt_pos]

lemma IsDiffusion.strip_value_le_groundState {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X)
    (hmom : ∀ t∈Ico (0 : ℝ) 1, (∫ ω,(gradient W γ t (X t ω))^2 ∂W.μ)=t)
    {T : ℝ} (hT : 0<T) (hT1 : T<1) :
    (∫ t in (0 : ℝ)..T,∫ ω,curvature W γ t (X t ω) ∂W.μ)≤groundStateValue := by
  have hreg := sourceStripRegularity W γ
  have hamom := hX.curvature_unit_moment_of_contact hreg hmom
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := hreg T ⟨hT.le,hT1⟩
  obtain ⟨hp,hl⟩ := hX.finite_gaussian_fixed_strip hT hT1 hG hD hLu hLa hDb hu ha
    (fun t ht ↦ hamom t ⟨ht.1,ht.2.trans_lt hT1⟩)
  apply le_of_tendsto hl
  filter_upwards [hp,eventually_gt_atTop (0 : ℕ)] with N hNpos hN
  exact shiftedCoefficientSum_le_groundState W γ hT.le hT1 hN
    (fun j hj ↦ (normalizer_pos_iff W γ T N j).mp (hNpos j hj))

theorem IsDiffusion.groundState_eq_parisi_of_contact {W : BrownianSpace}
    {γ : OrderParameter} {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X)
    (hmom : ∀ t∈Ico (0 : ℝ) 1, (∫ ω,(gradient W γ t (X t ω))^2 ∂W.μ)=t) :
    groundStateValue=parisi W γ := by
  have hreg := sourceStripRegularity W γ
  obtain ⟨U,hmart,hU,hU2,hP,hB,hA,hi,hl⟩ :=
    hX.parisi_value_assembly hreg hmom (hX.curvature_unit_moment_of_contact hreg hmom)
  refine le_antisymm (groundStateValue_le_parisi W γ) ?_
  apply le_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds
    (Ioi_mem_nhds (by norm_num : (0 : ℝ)<1))] with T hT1 hT
  exact hX.strip_value_le_groundState hmom hT hT1

theorem IsDiffusion.scalar_value_of_contact {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X)
    (hmom : ∀ t∈Ico (0 : ℝ) 1, (∫ ω,(gradient W γ t (X t ω))^2 ∂W.μ)=t) :
    ScalarValueConclusion W γ X := by
  have hreg := sourceStripRegularity W γ
  obtain ⟨U,hmart,hU,hU2,hP,hB,hA,hi,hl⟩ :=
    hX.parisi_value_assembly hreg hmom (hX.curvature_unit_moment_of_contact hreg hmom)
  refine ⟨SKValueG.groundStateSequence_tendsto,U,hmart,hU,hU2,?_,?_,?_,hi⟩
  · exact (hX.groundState_eq_parisi_of_contact hmom).trans hP
  · exact (hX.groundState_eq_parisi_of_contact hmom).trans hB
  · exact (hX.groundState_eq_parisi_of_contact hmom).trans hA

theorem IsDiffusion.finite_gaussian_of_contact {W : BrownianSpace}
    {γ : OrderParameter} {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X)
    (hmom : ∀ t∈Ico (0 : ℝ) 1, (∫ ω,(gradient W γ t (X t ω))^2 ∂W.μ)=t)
    {T : ℝ} (hT : 0<T) (hT1 : T<1) : FiniteGaussianConclusion W γ X T := by
  have hreg := sourceStripRegularity W γ
  have hamom := hX.curvature_unit_moment_of_contact hreg hmom
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := hreg T ⟨hT.le,hT1⟩
  obtain ⟨hp,hl⟩ := hX.finite_gaussian_fixed_strip hT hT1 hG hD hLu hLa hDb hu ha
    (fun t ht ↦ hamom t ⟨ht.1,ht.2.trans_lt hT1⟩)
  obtain ⟨U,hmart,hU,hU2,hP,hB,hA,hi,hend⟩ := hX.parisi_value_assembly hreg hmom hamom
  refine ⟨hp,hl,?_⟩
  rwa [hX.groundState_eq_parisi_of_contact hmom]

end SKValue

end

end OAI
