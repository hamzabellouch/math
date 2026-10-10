import OAI.Analysis.KadisonSimilarity.Derivation.CyclicGraphEmbedding
import Mathlib.Topology.Sequences

namespace OAI

/-! Points of the closed cyclic graph are limits of actual algebra orbits. -/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped Topology

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem exists_cyclicGraph_sequence
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (Ω : H) (ξ : K) (x : cyclicGraph σ ρ Ω ξ) :
    ∃ a : ℕ → A, Tendsto
      (fun n => pairRepresentation σ ρ (a n) (WithLp.toLp 2 (Ω, ξ))) atTop
      (𝓝 (x : RectangularSum H K)) := by
  classical
  have hx := x.property
  change (x : RectangularSum H K) ∈ closure
    (Set.range (orbitLinearMap (pairRepresentation σ ρ).range (WithLp.toLp 2 (Ω, ξ)))) at hx
  obtain ⟨y, hy, hlim⟩ := mem_closure_iff_seq_limit.mp hx
  choose b hb using hy
  choose a ha using fun n => (b n).property
  refine ⟨a, hlim.congr fun n => ?_⟩
  rw [← hb n]
  change (b n : RectangularSum H K →L[ℂ] RectangularSum H K) (WithLp.toLp 2 (Ω, ξ)) = _
  rw [← ha n]
  rfl

/-- Both coordinates of a graph point are limits of the same algebra orbit. -/
theorem exists_cyclicGraph_coordinate_limits
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (Ω : H) (ξ : K) (x : cyclicGraph σ ρ Ω ξ) :
    ∃ a : ℕ → A,
      Tendsto (fun n => σ (a n) Ω) atTop (𝓝 (x : RectangularSum H K).fst) ∧
      Tendsto (fun n => ρ (a n) ξ) atTop (𝓝 (x : RectangularSum H K).snd) := by
  obtain ⟨a, ha⟩ := exists_cyclicGraph_sequence σ ρ Ω ξ x
  refine ⟨a, ?_, ?_⟩
  · have h := ((WithLp.fstL 2 ℂ H K).continuous.tendsto
      (x : RectangularSum H K)).comp ha
    change Tendsto (fun n => (pairRepresentation σ ρ (a n)
      (WithLp.toLp 2 (Ω, ξ))).fst) atTop (𝓝 (x : RectangularSum H K).fst) at h
    simpa only [pairRepresentation_fst, WithLp.toLp_fst] using h
  · have h := ((WithLp.sndL 2 ℂ H K).continuous.tendsto
      (x : RectangularSum H K)).comp ha
    change Tendsto (fun n => (pairRepresentation σ ρ (a n)
      (WithLp.toLp 2 (Ω, ξ))).snd) atTop (𝓝 (x : RectangularSum H K).snd) at h
    simpa only [pairRepresentation_snd, WithLp.toLp_snd] using h

end KadisonSimilarity

end

end OAI
