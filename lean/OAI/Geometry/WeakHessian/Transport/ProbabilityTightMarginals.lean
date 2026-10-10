import Mathlib
import OAI.Geometry.WeakHessian.Transport.TruncatedQuadraticCost

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace WeakHessianTransport
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [ProperSpace X] [ProperSpace Y]
  [TopologicalSpace.SeparableSpace X] [TopologicalSpace.SeparableSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

lemma probability_isTight_of_marginals (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : Set (ProbabilityMeasure (X×Y)))
    (h0 : ∀ q ∈ S,(q : Measure (X×Y)).map Prod.fst = μ)
    (h1 : ∀ q ∈ S,(q : Measure (X×Y)).map Prod.snd = ν) :
    IsTightMeasureSet {((q:ProbabilityMeasure (X×Y)) : Measure (X×Y)) | q ∈ S} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  have hh : 0 < ε/2 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨K,hK,hKm⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    (isTightMeasureSet_singleton (μ := μ)) (ε/2) hh
  obtain ⟨L,hL,hLm⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    (isTightMeasureSet_singleton (μ := ν)) (ε/2) hh
  refine ⟨K×ˢL,hK.prod hL,?_⟩
  rintro _ ⟨q,hq,rfl⟩
  have he : (K×ˢL)ᶜ = (Prod.fst ⁻¹' Kᶜ) ∪ (Prod.snd ⁻¹' Lᶜ) := by ext p; simp only [mem_compl_iff,mem_prod,not_and_or,mem_union,mem_preimage]
  calc
    (q:Measure (X×Y)) (K×ˢL)ᶜ ≤ (q:Measure (X×Y)) (Prod.fst ⁻¹' Kᶜ)+(q:Measure (X×Y)) (Prod.snd ⁻¹' Lᶜ) := by rw [he]; exact measure_union_le _ _
    _ = μ Kᶜ+ν Lᶜ := by rw [←Measure.map_apply measurable_fst hK.measurableSet.compl,
        ←Measure.map_apply measurable_snd hL.measurableSet.compl,h0 q hq,h1 q hq]
    _ ≤ ε/2+ε/2 := add_le_add (hKm μ (mem_singleton μ)) (hLm ν (mem_singleton ν))
    _ = ε := ENNReal.add_halves ε

lemma exists_coupling_limit (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (qs : ℕ → ProbabilityMeasure (X×Y))
    (h0 : ∀ n,(qs n : Measure (X×Y)).map Prod.fst = μ)
    (h1 : ∀ n,(qs n : Measure (X×Y)).map Prod.snd = ν) :
    ∃ q : ProbabilityMeasure (X×Y), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (qs ∘ φ) atTop (𝓝 q) ∧
      (q:Measure (X×Y)).map Prod.fst = μ ∧ (q:Measure (X×Y)).map Prod.snd = ν := by
  have ht := probability_isTight_of_marginals μ ν (range qs)
    (by rintro _ ⟨n,rfl⟩; exact h0 n) (by rintro _ ⟨n,rfl⟩; exact h1 n)
  obtain ⟨q,_,φ,hφ,hlim⟩ := (isCompact_closure_of_isTightMeasureSet ht).tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  refine ⟨q,φ,hφ,hlim,?_,?_⟩
  · have H := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous (qs ∘ φ) q hlim
      (continuous_fst : Continuous (Prod.fst : X×Y → X))
    have he : (fun n => (qs (φ n)).map Prod.fst) = fun _ : ℕ => (⟨μ,inferInstance⟩ : ProbabilityMeasure X) := by
      funext n
      apply ProbabilityMeasure.toMeasure_injective
      simpa using h0 (φ n)
    change Tendsto (fun n => (qs (φ n)).map Prod.fst) atTop _ at H
    rw [he] at H
    simpa using congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique H tendsto_const_nhds)
  · have H := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous (qs ∘ φ) q hlim
      (continuous_snd : Continuous (Prod.snd : X×Y → Y))
    have he : (fun n => (qs (φ n)).map Prod.snd) = fun _ : ℕ => (⟨ν,inferInstance⟩ : ProbabilityMeasure Y) := by
      funext n
      apply ProbabilityMeasure.toMeasure_injective
      simpa using h1 (φ n)
    change Tendsto (fun n => (qs (φ n)).map Prod.snd) atTop _ at H
    rw [he] at H
    simpa using congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique H tendsto_const_nhds)
end WeakHessianTransport

namespace WeakHessianTransport
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]

lemma exists_proper_coupling_cost_of_hopf_bound (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (B : ℝ)
    (hdual : ∀ f : X →ᵇ ℝ, (∃ L : ℝ≥0, LipschitzWith L f) →
      (∫ x,hopfLax f 1 x ∂μ)-(∫ x,f x ∂ν) ≤ B/2) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧
      q.map Prod.fst = μ ∧ q.map Prod.snd = ν ∧
      (∫⁻ p, (edist p.1 p.2)^2 ∂(q:Measure (X×X))) ≤ ENNReal.ofReal B := by
  choose qs hp h0 h1 hc using exists_coupling_truncatedCost_of_hopf_bound μ ν B hdual
  let ps : ℕ → ProbabilityMeasure (X×X) := fun n => ⟨qs n,hp n⟩
  obtain ⟨q,φ,hφ,hlim,hq0,hq1⟩ := exists_coupling_limit μ ν ps h0 h1
  have hcost (k : ℕ) : (∫ p,truncatedQuadraticCost k p ∂(q:Measure (X×X))) ≤ B/2 := by
    have H := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim (truncatedQuadraticCost k)
    apply le_of_tendsto H
    filter_upwards [eventually_ge_atTop k] with n hn
    have hk : k ≤ φ n := hn.trans (hφ.id_le n)
    have hi (p : X×X) : truncatedQuadraticCost k p ≤ truncatedQuadraticCost (φ n) p := by
      exact min_le_min_left _ (Nat.cast_le.mpr hk)
    let := hp (φ n)
    exact (integral_mono ((truncatedQuadraticCost k).integrable (qs (φ n)))
      ((truncatedQuadraticCost (φ n)).integrable (qs (φ n))) hi).trans (hc (φ n))
  have hnn (k : ℕ) (p : X×X) : 0 ≤ truncatedQuadraticCost k p :=
    le_min (by positivity) (Nat.cast_nonneg k)
  have heavg : (∫⁻ p : X×X, ENNReal.ofReal (dist p.1 p.2^2/2) ∂(q:Measure (X×X))) ≤ ENNReal.ofReal (B/2) := by
    have hs (p : X×X) : ENNReal.ofReal (dist p.1 p.2^2/2) =
        ⨆ n : ℕ, ENNReal.ofReal (truncatedQuadraticCost n p) := by
      apply le_antisymm
      · obtain ⟨n,hn⟩ := exists_nat_gt (dist p.1 p.2^2/2)
        exact (le_iSup_of_le n (by simp only [truncatedQuadraticCost_apply, min_eq_left hn.le]; exact le_rfl))
      · exact iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)
    simp_rw [hs]
    rw [lintegral_iSup (fun n => (truncatedQuadraticCost n).continuous.measurable.ennreal_ofReal)]
    · apply iSup_le
      intro n
      rw [←ofReal_integral_eq_lintegral_ofReal ((truncatedQuadraticCost n).integrable (q:Measure (X×X)))
        (ae_of_all _ (hnn n))]
      exact ENNReal.ofReal_le_ofReal (hcost n)
    · intro a b hab p
      exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.mpr hab))
  refine ⟨q,inferInstance,hq0,hq1,?_⟩
  calc
    (∫⁻ p, (edist p.1 p.2)^2 ∂(q:Measure (X×X))) =
        ∫⁻ p : X×X, (2:ℝ≥0∞)*ENNReal.ofReal (dist p.1 p.2^2/2) ∂(q:Measure (X×X)) := by
      apply lintegral_congr
      intro p
      rw [edist_dist,←ENNReal.ofReal_pow dist_nonneg]
      rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,
        ←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      ring
    _ = 2*(∫⁻ p : X×X, ENNReal.ofReal (dist p.1 p.2^2/2) ∂(q:Measure (X×X))) := by
      rw [lintegral_const_mul _ (by fun_prop)]
    _ ≤ 2*ENNReal.ofReal (B/2) := by gcongr
    _ = ENNReal.ofReal B := by
      rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,
        ←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      ring
end WeakHessianTransport

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

end
end InlinedFile0

end OAI
