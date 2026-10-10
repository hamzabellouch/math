import Mathlib
import OAI.Probability.Ballisticity.Estimates.BufferChanceData
import OAI.Probability.Ballisticity.Estimates.Buffer
import OAI.Probability.Ballisticity.Walk.BufferGrowthArithmetic

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

theorem actual_buffer_excess {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ (κ : ℝ≥0) (α s g R : ℝ), 0 < κ ∧ κ ≤ 1 ∧ (∀ᵐ ω ∂environmentLaw ν, ∀ y u, κ ≤ (ω y).1 u) ∧ 0 < α ∧ 0 < s ∧
      0 < g ∧ g ≤ 1 ∧ 1 ≤ R ∧
      ∀ (a : ℝ) (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) a),
      let ε := 1-Real.exp (-(s*Real.log (1+α)/8))
      let root := bufferRootNode e f hef R a x hx
      let B := bufferTreeSuccess e f hef R (signedCoordinate f (x.2-x.1)) ε α g κ
        (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f) root
      ∃ W : Environment d → ℝ, Measurable W ∧ (∀ ω, 0 ≤ W ω) ∧
        Integrable (fun ω => Real.exp (W ω)) (environmentLaw ν) ∧
        (∀ᵐ ω ∂environmentLaw ν, ∀ n : ℕ, s/4*(n:ℝ)-successes B n ω ≤ W ω) ∧
        (∫ ω, Real.exp (W ω) ∂environmentLaw ν) ≤ 1+(1-Real.exp (-s/4))⁻¹ ∧
        (∀ᵐ ω ∂environmentLaw ν, ∀ n : ℕ,
          Real.log R+(s*Real.log (1+α)/8)*(n:ℝ)-W ω*(Real.log (1+α)+s*Real.log (1+α)/8) ≤
          Real.log (bufferCurrentNode e f hef R (signedCoordinate f (x.2-x.1)) ε α g κ
            (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f) root ω n).radius) := by
  obtain ⟨κ,hκ,hκae⟩ := environment_uniform_elliptic ν hue
  have hκ1 : κ ≤ 1 := by
    obtain ⟨ω,hω⟩ := hκae.exists
    exact (hω 0 e).trans (row_entry_le_one (ω 0) e)
  obtain ⟨α,s,hα,hs,hdata⟩ := actual_buffer_chance_data ν hue e f hef htrans
  let ε := 1-Real.exp (-(s*Real.log (1+α)/8))
  have hε := buffer_contraction_choice hα hs
  obtain ⟨g,R₀,hg,hg1,hR₀,hgood⟩ := hdata ε hε.1
  let R := max R₀ 1
  have hR : 0 < R := zero_lt_one.trans_le (le_max_right _ _)
  have hgood' : BufferChanceData ν e f α s ε g R := fun r hr => hgood r ((le_max_left _ _).trans hr)
  refine ⟨κ,α,s,g,R,hκ,hκ1,hκae,hα,hs,hg,hg1,le_max_right _ _,?_⟩
  intro a x hx
  let root := bufferRootNode e f hef R a x hx
  let B := bufferTreeSuccess e f hef R (signedCoordinate f (x.2-x.1)) ε α g κ
    (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f) root
  have hb := bufferTreeSuccess_measurable e f hef R (signedCoordinate f (x.2-x.1)) ε α g κ
    (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f) root
  have hstep := bufferTree_real_success ν e f hef hR (signedCoordinate f (x.2-x.1)) ε α g s hs.le
    hκ hκ1 hκae hg hg1 hε.1.le hgood' root le_rfl (bufferRootNode_valid e f hef R a x hx κ) rfl
  obtain ⟨W,hW,hW0,hWi,hWe,hWb⟩ := adaptive_failure_excess (environmentLaw ν) B hb hs hstep
  refine ⟨W,hW,hW0,hWi,hWe,hWb,?_⟩
  filter_upwards [hWe] with ω hω
  intro n
  exact bufferCurrentNode_log_growth e f hef hR hα hs (signedCoordinate f (x.2-x.1)) g κ
    (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f) root rfl ω (Set.mem_univ _) (W ω) hω n
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
lemma positiveBufferPlan_linear_lower {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ M : ℝ, 0 < M ∧ ∀ r : ℝ, 0 < r → r ≤ M*(positiveBufferPlan ν e f r+1) := by
  let ℓ := realPosition (step e)
  let μ := independentConditionedPairLaw ν ℓ
  let S := commonIncrementProcess ℓ f 0
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  have hi : Integrable S μ := independent_commonWordIncrement_integrable ν hue ℓ
    (signed_direction_unit e) htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) f
  have hn : 0 < μ {P | S P ≠ 0} := independent_commonWordIncrement_nonzero ν hue e f hef htrans
  let M := ∫ P, |S P| ∂μ
  have hM : 0 < M := integral_abs_pos_of_nonzero μ S hi hn
  refine ⟨M,hM,fun r hr => ?_⟩
  have hlow := fluctuationScale_lower μ S (measurable_commonIncrementProcess ℓ f 0) hi hn hr
  have hf := Nat.lt_floor_add_one (fluctuationScale μ S r)
  have hmax : (⌊fluctuationScale μ S r⌋₊:ℝ) ≤ positiveBufferPlan ν e f r := by
    exact_mod_cast (le_max_right 1 ⌊fluctuationScale μ S r⌋₊)
  have hh : r/M ≤ positiveBufferPlan ν e f r+1 := hlow.trans (le_of_lt (hf.trans_le (by linarith)))
  exact (div_le_iff₀ hM).mp hh |>.trans_eq (mul_comm _ _)
end DirectionalTransience

end

end

end OAI
