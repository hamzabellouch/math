import OAI.Analysis.KadisonKastler.ClosedExpectation
import OAI.Analysis.KadisonKastler.FiniteAveraging

namespace OAI

/-! # Averaging the two-dimensional projection expectations

Equal free joint laws give the two scalar pairings of each affine
projection expectation. These determine its coefficients independently
of the selected projection. Uniformly averaging the projections then
recovers exactly the common scalar trace.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {B : Type*} [CStarAlgebra B]

/-- Affine projection expectations with a common pair of trace values
average to the scalar given by their common trace. -/
theorem finiteAverage_affine_projections {ι : Type*} [Fintype ι] [Nonempty ι]
    (τ : FaithfulTracialState B) (p y : ι → B)
    (hp : ∀ i, IsStarProjection (p i)) {t c d : ℂ}
    (hptrace : ∀ i, τ.toLinearMap (p i) = t) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hpavg : finiteAverage p = t • (1 : B))
    (hy : ∀ i, ∃ α β : ℂ, y i = α • p i + β • (1 : B))
    (htrace : ∀ i, τ.toLinearMap (y i) = c)
    (hcompressed : ∀ i, τ.toLinearMap (p i * y i) = d) :
    finiteAverage y = c • (1 : B) := by
  classical
  let i₀ : ι := Classical.arbitrary ι
  obtain ⟨α, β, h₀⟩ := hy i₀
  have hformula (i : ι) : y i = α • p i + β • (1 : B) := by
    obtain ⟨γ, δ, hi⟩ := hy i
    have ht : τ.toLinearMap (α • p i₀ + β • (1 : B)) =
        τ.toLinearMap (γ • p i + δ • (1 : B)) := by rw [← h₀, ← hi, htrace, htrace]
    have hc : τ.toLinearMap (p i₀ * (α • p i₀ + β • (1 : B))) =
        τ.toLinearMap (p i * (γ • p i + δ • (1 : B))) := by
      rw [← h₀, ← hi, hcompressed, hcompressed]
    obtain ⟨rfl, rfl⟩ := affine_projection_coefficients_unique_between_traces τ τ (hp i₀) (hp i)
      ht0 ht1 (hptrace i₀) (hptrace i) ht hc
    exact hi
  have hscalar : α * t + β = c := by
    have hh := htrace i₀
    rwa [h₀, map_add, map_smul, map_smul, hptrace, τ.map_one,
      smul_eq_mul, smul_eq_mul, mul_one] at hh
  rw [show y = (fun i => α • p i + β • (1 : B)) from funext hformula]
  have hadd : finiteAverage (fun i => α • p i + β • (1 : B)) =
      α • finiteAverage p + β • (1 : B) := by
    simp only [finiteAverage, Finset.sum_add_distrib, ← Finset.smul_sum, smul_add]
    rw [smul_comm (Fintype.card ι : ℂ)⁻¹ α]
    congr 1
    simpa only [finiteAverage, ← Finset.smul_sum] using
      (finiteAverage_const (G := ι) (β • (1 : B)))
  rw [hadd, hpavg, smul_smul, ← add_smul, hscalar]

end

end KadisonKastler

end OAI
