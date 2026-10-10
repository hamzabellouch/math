import OAI.Analysis.IrrationalRotation.Couplings.CircleCouplingHybrid
import OAI.Analysis.IrrationalRotation.Analysis.RationalGraphs
import OAI.Analysis.IrrationalRotation.Operators.OperatorCompactTransfer

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace Invariant233.CircleCoupling
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

def sampleFiniteLaw (j : ℕ) : FiniteMeasure Sample := by
  letI := law_isProbabilityMeasure hp j
  exact ⟨law p j, inferInstance⟩

def hybridPairLaw (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (N : ℕ) : FiniteMeasure (Circle × Circle) :=
  (sampleFiniteLaw hp j).map (fun ω => (point p hr false ω, finiteHybridPoint p hr N ω))

def endpointPairLaw (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) :
    FiniteMeasure (Circle × Circle) :=
  (sampleFiniteLaw hp j).map (fun ω => (point p hr false ω, point p hr true ω))

lemma hybridPairLaw_fst (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) (N : ℕ) :
    (hybridPairLaw hp j hr N : Measure (Circle × Circle)).map Prod.fst =
      (law p j).map (point p hr false) := by
  change ((law p j).map _).map Prod.fst = _
  rw [Measure.map_map measurable_fst
    ((measurable_point hp hr false).prodMk (measurable_finiteHybridPoint hp hr N))]
  rfl

lemma hybridPairLaw_snd (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) (N : ℕ) :
    (hybridPairLaw hp j hr N : Measure (Circle × Circle)).map Prod.snd =
      (law p j).map (finiteHybridPoint p hr N) := by
  change ((law p j).map _).map Prod.snd = _
  rw [Measure.map_map measurable_snd
    ((measurable_point hp hr false).prodMk (measurable_finiteHybridPoint hp hr N))]
  rfl

lemma tendsto_hybridPairLaw (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) :
    Tendsto (hybridPairLaw hp j hr) atTop (𝓝 (endpointPairLaw hp j hr)) := by
  apply HybridLaw.tendsto_finiteMeasure_map_of_ae_tendsto
  · intro N
    exact (measurable_point hp hr false).prodMk (measurable_finiteHybridPoint hp hr N)
  · exact (measurable_point hp hr false).prodMk (measurable_point hp hr true)
  · exact Eventually.of_forall fun ω => tendsto_const_nhds.prodMk_nhds
      (tendsto_finiteHybridPoint hp hr ω)

lemma hybridPairLaw_uniform_fst (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) :
    UniformlyAbsolutelyContinuous circleMeasure
      (fun N => (hybridPairLaw hp j hr N : Measure (Circle × Circle)).map Prod.fst) := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := uniformlyAbsolutelyContinuous_hybrids hp j hr ε hε
  refine ⟨δ, hδ, ?_⟩
  intro A hA hμ N
  change ((hybridPairLaw hp j hr N : Measure (Circle × Circle)).map Prod.fst) A < ε
  rw [hybridPairLaw_fst hp j hr N]
  exact hb A hA hμ (fun _ => false)

lemma hybridPairLaw_uniform_snd (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) :
    UniformlyAbsolutelyContinuous circleMeasure
      (fun N => (hybridPairLaw hp j hr N : Measure (Circle × Circle)).map Prod.snd) := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := uniformlyAbsolutelyContinuous_hybrids hp j hr ε hε
  refine ⟨δ, hδ, ?_⟩
  intro A hA hμ N
  change ((hybridPairLaw hp j hr N : Measure (Circle × Circle)).map Prod.snd) A < ε
  rw [hybridPairLaw_snd hp j hr N]
  exact hb A hA hμ (finiteHybridChoice N)

lemma finiteHybrid_rational_graph (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (N : ℕ) (ω : Sample) :
    ∃ z : ℤ, finiteHybridPoint p hr N ω =
      point p hr false ω + p.rationalTranslation (N + 1) z := by
  rw [finiteHybridPoint_eq]
  have h := MixedRadix.circleValue_hybrid_eq_add_int_div hr
    (digits p hr false ω) (digits p hr true ω) (N + 1)
  simpa only [MixedRadix.denominator_radices hp.frequency_zero hp.frequency_divisible,
    rationalTranslation, point] using h

lemma ae_hybridPairLaw_graph (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) (N : ℕ) :
    ∀ᵐ z ∂(hybridPairLaw hp j hr N : Measure (Circle × Circle)),
      ∃ r : ℤ, z.2 = z.1 + p.rationalTranslation (N + 1) r := by
  change ∀ᵐ z ∂(law p j).map
    (fun ω => (point p hr false ω, finiteHybridPoint p hr N ω)), _
  apply (ae_map_iff
    ((measurable_point hp hr false).prodMk (measurable_finiteHybridPoint hp hr N)).aemeasurable ?_).mpr
  · exact Eventually.of_forall (finiteHybrid_rational_graph hp hr N)
  · simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun r =>
      measurableSet_eq_fun measurable_snd (measurable_fst.add measurable_const)

lemma ae_hybridPairLaw_ratio_cap (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (N : ℕ) (k : ℤ) :
    ∀ᵐ z ∂(hybridPairLaw hp j hr N : Measure (Circle × Circle)),
      p.floorCocycle θ k z.2 / p.floorCocycle θ k z.1 ≤ 1 := by
  change ∀ᵐ z ∂(law p j).map
    (fun ω => (point p hr false ω, finiteHybridPoint p hr N ω)), _
  apply (ae_map_iff
    ((measurable_point hp hr false).prodMk (measurable_finiteHybridPoint hp hr N)).aemeasurable ?_).mpr
  · filter_upwards [ae_finiteHybrid_ratio_cap hp j hr N] with ω hω
    exact (hω k).2
  · exact measurableSet_le
      (((hp.measurable_parameter_cocycle k).comp measurable_snd).div
        ((hp.measurable_parameter_cocycle k).comp measurable_fst)) measurable_const

lemma ae_endpointPairLaw_ratio_cap (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (k : ℤ) :
    ∀ᵐ z ∂(endpointPairLaw hp j hr : Measure (Circle × Circle)),
      p.floorCocycle θ k z.2 / p.floorCocycle θ k z.1 ≤ 1 := by
  change ∀ᵐ z ∂(law p j).map (fun ω => (point p hr false ω, point p hr true ω)), _
  apply (ae_map_iff
    ((measurable_point hp hr false).prodMk (measurable_point hp hr true)).aemeasurable ?_).mpr
  · filter_upwards [ae_endpoint_ratio_cap hp j hr] with ω hω
    exact (hω k).2
  · exact measurableSet_le
      (((hp.measurable_parameter_cocycle k).comp measurable_snd).div
        ((hp.measurable_parameter_cocycle k).comp measurable_fst)) measurable_const

theorem orderedCouplingIdentities_of_rational
    (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber)
    (hF : ∀ x, IsStarProjection (F x))
    (hFm : ∀ k : ℤ, Measurable (fun x => F x (lp.single 2 k 1)))
    (hgraph : p.RationalGraphIdentities θ F) :
    OrderedCouplingIdentities p θ hr F := by
  intro j
  have hzero (N : ℕ) : ∀ᵐ z ∂(hybridPairLaw hp j hr N : Measure (Circle × Circle)),
      (1 - F z.2).comp ((ratioDiagonal (p.floorCocycle θ) z).comp (F z.1)) = 0 := by
    apply Fields.ae_pair_relation_of_countable_graphs
      (fun x y => (1 - F y).comp ((ratioDiagonal (p.floorCocycle θ) (x, y)).comp (F x)) = 0)
      (fun r : ℤ => fun x => x + p.rationalTranslation (N + 1) r)
      ((hybridPairLaw_uniform_fst hp j hr).absolutelyContinuous N)
    · intro r
      filter_upwards [hgraph] with x hx
      exact hx (N + 1) (by omega) r
    · exact ae_hybridPairLaw_graph hp j hr N
  have hlim := CompactTransfer.compact_operator_transfer circleMeasure F hF
    (p.floorCocycle θ) (fun k x => p.floorCocycle_pos θ k x)
    hp.measurable_parameter_cocycle hFm (tendsto_hybridPairLaw hp j hr)
    (hybridPairLaw_uniform_fst hp j hr) (hybridPairLaw_uniform_snd hp j hr)
    1 (by norm_num) (ae_hybridPairLaw_ratio_cap hp j hr)
    (ae_endpointPairLaw_ratio_cap hp j hr) hzero
  have hpull := ae_of_ae_map
    ((measurable_point hp hr false).prodMk (measurable_point hp hr true)).aemeasurable hlim
  filter_upwards [hpull, ae_endpoint_ratio_cap hp j hr] with ω hω hcap
  exact ⟨hω, hcap⟩

theorem exists_ordered_coupling_field
    {P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert}
    (hmem : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
    (hT : (1 - P) * p.measurableOperator θ hp * P = 0) :
    ∃ (hr : ∀ i, 0 < MixedRadix.radices p.q i)
      (F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber),
      (∀ x, IsStarProjection (F x)) ∧
      (∀ x, ‖F x‖ ≤ ‖P‖) ∧
      (∀ v : Rotation.Fiber, StronglyMeasurable fun x => F x v) ∧
      (∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) ∧
      OrderedCouplingIdentities p θ hr F := by
  obtain ⟨F, hproj, hnorm, hmeas, hrep, hgraph⟩ := hp.exists_rational_graph_field hmem hP hT
  let hr := MixedRadix.radices_pos hp.q_pos hp.frequency_increasing hp.frequency_divisible
  exact ⟨hr, F, hproj, hnorm, hmeas, hrep,
    orderedCouplingIdentities_of_rational hp hr F hproj
      (fun k => (hmeas (lp.single 2 k 1)).measurable) hgraph⟩

end Invariant233.CircleCoupling

end

end OAI
