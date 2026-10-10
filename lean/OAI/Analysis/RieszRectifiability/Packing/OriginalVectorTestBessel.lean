import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.VectorBesselTransfer
import OAI.Analysis.RieszRectifiability.Packing.OriginalTestBessel

namespace OAI

/-!
# Vector-valued Bessel estimates for dyadic oscillation tests

The scalar Bessel estimate transfers through the Euclidean orthonormal basis
to directional pairings with vector-valued L² functions. The normalization
retains the radius powers and interaction-packing constant, and the resulting
estimate applies to the hard-truncated Riesz transform under its L² bound.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem DyadicOscillationTests.vector_bessel {ι : Type*} {n d : ℕ}
    [Nontrivial (Ambient d)] {μ : Measure (Ambient d)} {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hc : 0 < c) (hJ : 0 < J) (s : Finset ι)
    (u : Ambient d → Ambient d) (hu : MemLp u 2 μ)
    (e : ι → Ambient d) (he : ∀ i ∈ s, ‖e i‖ ≤ 1) :
    ∑ i ∈ s, (∫ x, F.test i x * inner ℝ (e i) (u x) ∂μ) ^ 2 / F.radius i ^ n ≤
      (4 * (G * J ^ (n + 1) * (2 * J + 1) ^ 2) * interactionPackingConstant n C G c J) *
        ∫ x, ‖u x‖ ^ 2 ∂μ := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  have hh := finite_vector_bessel_of_scalar (EuclideanSpace.basisFun (Fin d) ℝ) μ s
    (F.normalized n hJ).test (fun i => ((F.normalized n hJ).memLp_integrable i).1) _
    (fun v hv => (F.normalized n hJ).bessel C G hC hg hlower hc hJ (by positivity) s v hv)
    u hu e he
  simpa only [F.normalized_pairing_sq n hJ] using! hh

theorem DyadicOscillationTests.native_truncation_bessel {ι : Type*} {n d : ℕ}
    [Nontrivial (Ambient d)] {μ : Measure (Ambient d)} {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hc : 0 < c) (hJ : 0 < J) (s : Finset ι) (D : ℝ≥0)
    (hR : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated n μ ε f) 2 μ ∧
        eLpNorm (truncated n μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ)
    (ε : ℝ) (hε : 0 < ε) (f : Ambient d → ℝ) (hf : MemLp f 2 μ)
    (e : ι → Ambient d) (he : ∀ i ∈ s, ‖e i‖ ≤ 1) :
    ∑ i ∈ s, (∫ x, F.test i x * inner ℝ (e i) (truncated n μ ε f x) ∂μ) ^ 2 /
      F.radius i ^ n ≤
      ((4 * (G * J ^ (n + 1) * (2 * J + 1) ^ 2) * interactionPackingConstant n C G c J) *
        (D : ℝ) ^ 2) * ∫ x, f x ^ 2 ∂μ := by
  obtain ⟨hT, hN⟩ := hR ε hε f hf
  have hB : 0 ≤ 4 * (G * J ^ (n + 1) * (2 * J + 1) ^ 2) *
      interactionPackingConstant n C G c J := by
    unfold interactionPackingConstant
    have hG := hg.1
    positivity
  calc
    _ ≤ _ := F.vector_bessel C G hC hg hlower hc hJ s _ hT e he
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left
        (vector_sq_integral_of_native_norm_bound μ f _ hf hT D hN) hB
      convert! hh using 1
      ring

end

end RieszRectifiability

end OAI
