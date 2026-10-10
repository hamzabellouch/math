import Mathlib
import OAI.Analysis.WeakInfiniteness.UniformModels
import OAI.Analysis.WeakInfiniteness.WordTensorDensity

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open Filter

open scoped Topology

section UniformCutEstimate

variable {B C : Type 1} [CStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder C] [StarOrderedRing C]

omit [PartialOrder C] [StarOrderedRing C] in
lemma tensorCut_wordTensor (s : Finset (List Bool)) (c : List Bool → C) (e : C) :
    tensorCut e (wordTensor s c) = wordTensor s (fun w => c w - c w * e) := by
  change tensorCutLinear e (∑ w ∈ s, minimalElementary (universalWord w) (c w)) = _
  rw [map_sum]
  unfold wordTensor
  apply Finset.sum_congr rfl
  intro w _hw
  exact tensorCut_elementary e (c w) (universalWord w)

lemma wordTensorCost_cut_le (s : Finset (List Bool)) (c : List Bool → C)
    (e : C) (he : 0 ≤ e) (hen : ‖e‖ ≤ 1) :
    wordTensorCost s (fun w => c w - c w * e) ≤ wordTensorCost s c := by
  unfold wordTensorCost
  apply Finset.sum_le_sum
  intro w _hw
  exact mul_le_mul_of_nonneg_right (norm_sub_mul_of_pos_contraction (c w) e he hen)
    (Nat.cast_nonneg _)

lemma norm_tensorCut_wordTensor_le_of_models (s : Finset (List Bool)) (c : List Bool → C)
    (v : B) (hv : ‖v‖ ≤ 1) (φ : UniversalContraction →⋆ₐ[ℂ] B)
    (hφ : φ universalContractionGenerator = v) {θ : ℝ} (hθ : 0 ≤ θ)
    (hmodels : FiniteContractionModels B v θ) (e : C) (he : 0 ≤ e) (hen : ‖e‖ ≤ 1) :
    ‖tensorCut e (wordTensor s c)‖ ≤
      ‖minimalMapLeft φ.toNonUnitalStarAlgHom (tensorCut e (wordTensor s c))‖ +
        wordTensorCost s c * θ := by
  rw [tensorCut_wordTensor]
  exact (norm_wordTensor_le_of_models s (fun w => c w - c w * e) v hv φ hφ hθ hmodels).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right (wordTensorCost_cut_le s c e he hen) hθ))

end UniformCutEstimate

structure ExactModelData (θ : ℝ) where
  Carrier : Type 1
  [cStarAlgebra : CStarAlgebra Carrier]
  v : Carrier
  norm_v : ‖v‖ ≤ 1
  exactAlgebra : Exact Carrier
  models : FiniteContractionModels Carrier v θ

attribute [instance] ExactModelData.cStarAlgebra

lemma exact_universal_of_arbitrarily_good_models
    (hall : ∀ θ : ℝ, 0 < θ → Nonempty (ExactModelData θ)) : Exact UniversalContraction := by
  intro C D _ _ q hq z hz
  let := CStarAlgebra.spectralOrder C
  let := CStarAlgebra.spectralOrderedRing C
  let I := kernelAlgebra q
  let := CStarAlgebra.spectralOrder I
  let := CStarAlgebra.spectralOrderedRing I
  let l := CStarAlgebra.approximateUnit I
  have hl := CStarAlgebra.increasingApproximateUnit I
  let : l.NeBot := hl.toIsApproximateUnit.neBot
  let e : I → C := Subtype.val
  have he : ∀ᶠ i in l, 0 ≤ e i ∧ ‖e i‖ ≤ 1 := by
    filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with i hi hn
    refine ⟨?_, hn⟩
    obtain ⟨x,hx⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hi
    have hi' : e i = star (e x) * e x := congrArg Subtype.val hx
    rw [hi']
    exact star_mul_self_nonneg _
  have happ : ∀ c : C, q c = 0 → Tendsto (fun i => c * e i) l (𝓝 c) := by
    intro c hc
    let x : I := ⟨c,hc⟩
    exact continuous_subtype_val.tendsto x |>.comp (hl.tendsto_mul_left x)
  apply tensor_mem_ideal_of_cuts l e q (fun i => i.property) z
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨c,hc⟩ := wordTensorLinear_range_dense.exists_dist_lt z (by positivity : 0 < ε/4)
  let s := c.support
  let w := wordTensor s c
  have hzw : ‖z-w‖ < ε/4 := by
    simpa only [dist_eq_norm, wordTensorLinear_apply, w, s, wordTensor] using hc
  let cost := wordTensorCost s c
  have hc0 : 0 ≤ cost := wordTensorCost_nonneg s c
  let θ := (ε/4)/(cost+1)
  have hθ : 0 < θ := div_pos (by positivity) (by positivity)
  have hcost : cost * θ ≤ ε/4 := by
    have heq : (cost+1)*θ = ε/4 := mul_div_cancel₀ _ (by positivity)
    nlinarith [le_of_lt hθ]
  obtain ⟨M⟩ := hall θ hθ
  let := CStarAlgebra.spectralOrder M.Carrier
  let := CStarAlgebra.spectralOrderedRing M.Carrier
  let φ := universalContractionMap M.v M.norm_v
  have hφ : φ universalContractionGenerator = M.v := universalContractionMap_generator _ _
  let Φ : MinimalTensor UniversalContraction C →⋆ₙₐ[ℂ] MinimalTensor M.Carrier C :=
    minimalMapLeft φ.toNonUnitalStarAlgHom
  have hmem : (Φ z).val ∈ tensorKernelIdeal (A := M.Carrier) q := by
    apply M.exactAlgebra C D q hq
    intro π
    exact hz (π.precompLeft φ.toNonUnitalStarAlgHom)
  have hcuts := tensorCut_tendsto_zero_on_ideal l e he q happ (Φ z) hmem
  have hsmall : ∀ᶠ i in l, ‖Φ (tensorCut (e i) z)‖ < ε/4 := by
    have h := Metric.tendsto_nhds.mp hcuts (ε/4) (by positivity)
    filter_upwards [h] with i hi
    simpa only [Φ, minimalMapLeft_tensorCut, dist_zero_right] using hi
  filter_upwards [he,hsmall] with i hi his
  rw [dist_zero_right]
  have hdiff : ‖tensorCut (e i) z - tensorCut (e i) w‖ ≤ ‖z-w‖ := by
    change ‖tensorCutLinear (e i) z - tensorCutLinear (e i) w‖ ≤ _
    rw [← map_sub]
    exact norm_tensorCut_le (e i) hi.1 hi.2 (z-w)
  have hΦdiff : ‖Φ (tensorCut (e i) w) - Φ (tensorCut (e i) z)‖ ≤ ‖z-w‖ := by
    rw [← map_sub]
    exact (NonUnitalStarAlgHom.norm_apply_le Φ _).trans ((norm_sub_rev _ _).le.trans hdiff)
  have hmodel := norm_tensorCut_wordTensor_le_of_models s c M.v M.norm_v φ hφ
    (le_of_lt hθ) M.models (e i) hi.1 hi.2
  have hm : ‖Φ (tensorCut (e i) w)‖ ≤ ‖Φ (tensorCut (e i) z)‖ + ‖z-w‖ :=
    (norm_le_norm_add_norm_sub' _ _).trans (add_le_add le_rfl hΦdiff)
  have hn := norm_le_norm_add_norm_sub' (tensorCut (e i) z) (tensorCut (e i) w)
  change ‖tensorCut (e i) w‖ ≤ ‖Φ (tensorCut (e i) w)‖ + cost * θ at hmodel
  linarith

theorem exists_uniform_gap_one :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (B : Type 1) [CStarAlgebra B] (v : B),
      ‖v‖ ≤ 1 → Exact B → ¬ FiniteContractionModels B v γ := by
  classical
  by_contra h
  have hall : ∀ θ : ℝ, 0 < θ → Nonempty (ExactModelData θ) := by
    intro θ hθ
    by_contra hn
    apply h
    refine ⟨θ,hθ,?_⟩
    intro B hB v hv hExact hmodels
    exact hn ⟨{ Carrier := B, v := v, norm_v := hv, exactAlgebra := hExact, models := hmodels }⟩
  exact universalContraction_not_exact (exact_universal_of_arbitrarily_good_models hall)

end

end WeakPureInfiniteness
end

end OAI
