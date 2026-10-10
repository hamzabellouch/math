import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.OriginalDyadicTests
import OAI.Analysis.RieszRectifiability.Packing.ADTestFamilyBessel

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem DyadicOscillationTests.bessel {ι : Type*} {n d : ℕ}
    [Nontrivial (Ambient d)] {μ : Measure (Ambient d)} {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hc : 0 < c) (hJ : 0 < J) (s : Finset ι)
    (u : Ambient d → ℝ) (hu : MemLp u 2 μ) :
    ∑ i ∈ s, (∫ x, F.test i x * u x ∂μ) ^ 2 / F.radius i ^ n ≤
      (4 * (G * J ^ (n + 1) * (2 * J + 1) ^ 2) * interactionPackingConstant n C G c J) *
        ∫ x, u x ^ 2 ∂μ := by
  have h := (F.normalized n hJ).bessel C G hC hg hlower hc hJ (by positivity) s u hu
  simpa only [F.normalized_pairing_sq n hJ] using! h

theorem DyadicOscillationTests.packing_of_large_pairings {ι : Type*} {n d : ℕ}
    [Nontrivial (Ambient d)] {μ : Measure (Ambient d)} {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hc : 0 < c) (hJ : 0 < J) (s : Finset ι)
    (u : Ambient d → ℝ) (hu : MemLp u 2 μ) (v : ℝ) (hv : 0 < v)
    (hlarge : ∀ i ∈ s, v * F.radius i ^ n ≤ |∫ x, F.test i x * u x ∂μ|) :
    ∑ i ∈ s, F.radius i ^ n ≤
      ((4 * (G * J ^ (n + 1) * (2 * J + 1) ^ 2) * interactionPackingConstant n C G c J) *
        ∫ x, u x ^ 2 ∂μ) / v ^ 2 := by
  apply (F.normalized n hJ).packing_of_large_pairings C G hC hg hlower hc hJ
    (by positivity) s u hu v hv
  intro i hi
  rw [F.normalized_pairing_sq n hJ]
  change v ^ 2 * F.radius i ^ n ≤ _
  apply (le_div_iff₀ (pow_pos (F.radius_pos i) n)).mpr
  have h := hlarge i hi
  have hnonneg : 0 ≤ v * F.radius i ^ n :=
    mul_nonneg hv.le (pow_nonneg (F.radius_pos i).le n)
  have hs := mul_self_le_mul_self hnonneg h
  nlinarith [sq_abs (∫ x, F.test i x * u x ∂μ)]

end

end RieszRectifiability

end OAI
