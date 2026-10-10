import OAI.GroupTheory.PolycyclicRecognition.Algebra.GradedGeneratorLimit
import Mathlib.Topology.UniformSpace.CompactConvergence

namespace OAI

/-! # Convergence of horizontal flows in graded coordinates -/

noncomputable section

namespace PolycyclicRecognition

open Filter Set Module
open scoped Topology

variable {n : ℕ}

/-- Right multiplication along the exponential line with velocity `v`,
recorded jointly in its base point and time. -/
def dynkinFlowMap {c : ℕ} (a : DynkinCoefficients c 2)
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (v : (Fin n → ℝ)) : C((Fin n → ℝ) × ℝ, (Fin n → ℝ)) :=
  ⟨fun z => dynkinProduct a B z.1 (z.2 • v),
    continuous_dynkinProduct a _ _ _ continuous_const continuous_fst
      (continuous_snd.smul continuous_const)⟩

/-- The polynomial flow depends continuously on its bracket and velocity
in the topology of uniform convergence on compact sets. -/
theorem continuous_dynkinFlowMap {c : ℕ} (a : DynkinCoefficients c 2) :
    Continuous (fun p : ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (Fin n → ℝ) => dynkinFlowMap (n := n) a p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (Fin n → ℝ)) × ((Fin n → ℝ) × ℝ) =>
    dynkinProduct a z.1.1 z.2.1 (z.2.2 • z.1.2))
  exact continuous_dynkinProduct (P := (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (Fin n → ℝ)) × ((Fin n → ℝ) × ℝ))
    a (fun z => z.1.1) (fun z => z.2.1) (fun z => z.2.2 • z.1.2)
    continuous_fst.fst continuous_snd.fst
    (continuous_snd.snd.smul continuous_fst.snd)

theorem dynkinFlowMap_tendsto {c : ℕ} (a : DynkinCoefficients c 2)
    {ι : Type*} {l : Filter ι} {B : ι → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    {B₀ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} {v : ι → (Fin n → ℝ)} {v₀ : (Fin n → ℝ)}
    (hB : Tendsto B l (𝓝 B₀)) (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun i => dynkinFlowMap (n := n) a (B i) (v i)) l (𝓝 (dynkinFlowMap (n := n) a B₀ v₀)) := by
  have hp : Tendsto (fun i => (B i, v i)) l (𝓝 (B₀, v₀)) := hB.prodMk_nhds hv
  simpa only [Function.comp_def] using
    ((continuous_dynkinFlowMap (n := n) a).tendsto (B₀, v₀)).comp hp

/-- Simultaneous convergence of base points and times on any fixed compact
set. This is the flow convergence used by chart profiles. -/
theorem dynkinFlowMap_tendstoUniformlyOn {c : ℕ} (a : DynkinCoefficients c 2)
    {ι : Type*} {l : Filter ι} {B : ι → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    {B₀ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} {v : ι → (Fin n → ℝ)} {v₀ : (Fin n → ℝ)}
    (hB : Tendsto B l (𝓝 B₀)) (hv : Tendsto v l (𝓝 v₀))
    {K : Set ((Fin n → ℝ) × ℝ)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun i z => dynkinProduct a (B i) z.1 (z.2 • v i))
      (fun z => dynkinProduct a B₀ z.1 (z.2 • v₀)) l K :=
  (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp
    (dynkinFlowMap_tendsto (n := n) a hB hv)) K hK

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- Actual rescaled exponential lines tend to the line of the degree-one
part of their velocity, with the limiting graded multiplication. -/
theorem rescaled_horizontal_flow_tendstoUniformlyOn
    {c : ℕ} (a : DynkinCoefficients c 2) (b : Basis (Fin n) ℝ L)
    (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (v : L) (hv : ∀ j, b.repr v j ≠ 0 → 1 ≤ cost j)
    {K : Set ((Fin n → ℝ) × ℝ)} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun r z => dynkinProduct a (basisBracket (exponentialRescaleBasis b cost r))
        z.1 (z.2 • (exponentialRescaleBasis b cost r).equivFun (Real.exp r • v)))
      (fun z => dynkinProduct a (gradedCoordinateBracket b cost)
        z.1 (z.2 • gradedGenerator b cost 1 v)) atTop K := by
  apply dynkinFlowMap_tendstoUniformlyOn (n := n) a (basisBracket_rescale_tendsto b cost hweight)
    (v₀ := gradedGenerator b cost 1 v) ?_ hK
  simpa only [mul_one] using rescaled_generator_tendsto b cost 1 v hv

end PolycyclicRecognition

end

end OAI
