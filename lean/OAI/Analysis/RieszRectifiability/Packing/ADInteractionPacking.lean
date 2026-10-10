import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.NormalizedGramDecay

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def interactionPackingConstant (n : ℕ) (C G c J : ℝ) : ℝ :=
  (C / c ^ n) * G * (2 * J + c) ^ n

theorem finite_AD_fine_interaction_mass {ι : Type*} {d : ℕ}
    (n : ℕ) (C G : ℝ) (hC : 0 < C) (μ : Measure (Ambient d))
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (s : Finset ι) (z : ι → Ambient d) (r : ι → ℝ) (c J : ℝ) (hc : 0 < c) (hJ : 0 < J)
    (hz : ∀ i ∈ s, z i ∈ μ.support) (hr : ∀ i ∈ s, 0 < r i)
    (hadmissible : ∀ i ∈ s, AdmissibleRadius μ (c * r i))
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (hsmall : ∀ i ∈ s, r i ≤ R)
    (hnear : ∀ i ∈ s, dist (z i) a ≤ J * R + J * r i)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → c * r i + c * r j ≤ dist (z i) (z j)) :
    ∑ i ∈ s, (r i) ^ n ≤ interactionPackingConstant n C G c J * R ^ n := by
  have hcontained : ∀ i ∈ s, dist (z i) a + c * r i ≤ (2 * J + c) * R := by
    intro i hi
    have hjr := mul_le_mul_of_nonneg_left (hsmall i hi) hJ.le
    have hcr := mul_le_mul_of_nonneg_left (hsmall i hi) hc.le
    linarith [hnear i hi]
  have h := finite_AD_core_mass_packing n C G hC μ hg hlower s z r c hc hz hr hadmissible
    a ((2 * J + c) * R) (by positivity) hcontained hsep
  simpa only [interactionPackingConstant, mul_pow, mul_assoc] using! h

theorem finite_AD_coarse_interaction_card {ι : Type*} {d : ℕ}
    (n : ℕ) (C G : ℝ) (hC : 0 < C) (μ : Measure (Ambient d))
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (s : Finset ι) (z : ι → Ambient d) (q c J : ℝ) (hq : 0 < q) (hc : 0 < c) (hJ : 0 < J)
    (hz : ∀ i ∈ s, z i ∈ μ.support) (hadmissible : AdmissibleRadius μ (c * q))
    (a : Ambient d) (R : ℝ) (hRq : R ≤ q)
    (hnear : ∀ i ∈ s, dist (z i) a ≤ J * R + J * q)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → c * q + c * q ≤ dist (z i) (z j)) :
    (s.card : ℝ) ≤ interactionPackingConstant n C G c J := by
  have hnear' : ∀ i ∈ s, dist (z i) a ≤ J * q + J * q := by
    intro i hi
    exact (hnear i hi).trans (add_le_add (mul_le_mul_of_nonneg_left hRq hJ.le) le_rfl)
  have h := finite_AD_fine_interaction_mass n C G hC μ hg hlower s z (fun _ => q) c J hc hJ
    hz (fun _ _ => hq) (fun _ _ => hadmissible) a q hq (fun _ _ => le_rfl) hnear' hsep
  simp only [Finset.sum_const, nsmul_eq_mul] at h
  exact (mul_le_mul_iff_left₀ (pow_pos hq n)).mp h

end

end RieszRectifiability

end OAI
