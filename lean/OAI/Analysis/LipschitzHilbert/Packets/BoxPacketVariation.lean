import OAI.Analysis.LipschitzHilbert.Estimates.BoxPolynomialWeight
import OAI.Analysis.LipschitzHilbert.Estimates.BoxSynthesisEnergy

namespace OAI

/-! Short-scale Hilbert packet variation from the explicit coefficient
budget and packet envelopes, retaining the horizontal and transverse
decay of one center box. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert

theorem box_packet_variation (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → κ → Type)
      [Fintype κ] [∀ j k, Fintype (ι j k)]
      (c : ∀ j k, ι j k → ℂ) (f : ∀ j k, ι j k → SchwartzMap ℝ ℂ)
      (s rho : ∀ j k, ι j k → ℝ) (len : Fin N → ℝ)
      (u r offset C D T B : ℝ) (q : ℕ),
      (∀ j, 0 < len j) → 0 < r → (∀ j k, ∀ _ : ι j k, len j ≤ r) →
      (∀ j k i, 0 < rho j k i) → (∀ j k i, rho j k i ≤ T) →
      (∀ j k i, |s j k i - (u + r * offset)| ≤ r) → 0 ≤ D → 0 ≤ T →
      (∀ j k x, ∑ i, rho j k i * lineEnvelope (s j k i) (len j) (1 + 2 * q) x ≤ D) →
      (∀ j k i x, ‖f j k i x‖ ≤ C *
        (rho j k i * lineEnvelope (s j k i) (len j) (1 + 2 * q) x)) →
      (∑ j, len j * ∑ k, ∑ i, ‖c j k i‖ ^ 2 ≤ B * r) →
      (∀ j k i ξ, |ξ| < lo * (2 : ℝ) ^ j.val → 𝓕 (f j k i) ξ = 0) →
      (∀ j k i ξ, hi * (2 : ℝ) ^ j.val < |ξ| → 𝓕 (f j k i) ξ = 0) →
      ENNReal.ofReal ((((1 + |offset|) ^ 2 / 8) ^ q) ^ 2) *
        (∫⁻ x in Icc (u - r) (u + r), ENNReal.ofReal (finiteCubicVariation
          (fun n => hilbertPartialBandSum
            (fun j k => packetSynthesis (c j k) (f j k)) n x) N) ^ (2 / 3 : ℝ)) ≤
        (K : ℝ≥0∞) * ENNReal.ofReal (D * C ^ 2 * 16 ^ q * Real.pi * T * (B * r)) := by
  obtain ⟨K,hK,hlocal⟩ := localized_dyadic_hilbert_variation hL hlo hhi
  refine ⟨K,hK,?_⟩
  intro N κ ι instκ instι c f s rho len u r offset C D T B q
    hlen hr hlenr hrho hrhoT hcenter hD hT hover henv hbudget hlow hhigh
  have hbudget' : (∑ jk : Fin N × κ, len jk.1 * ∑ i, ‖c jk.1 jk.2 i‖ ^ 2) ≤ B * r := by
    rw [Fintype.sum_prod_type]
    simpa only [← Finset.mul_sum] using hbudget
  have henergy := box_synthesis_energy
    (fun jk : Fin N × κ => c jk.1 jk.2) (fun jk => f jk.1 jk.2)
    (fun jk => s jk.1 jk.2) (fun jk => rho jk.1 jk.2) (fun jk => len jk.1)
    (u + r * offset) r C D T B q (fun jk => hlen jk.1) hr
    (fun jk => hlenr jk.1 jk.2) (fun jk => hrho jk.1 jk.2)
    (fun jk => hrhoT jk.1 jk.2) (fun jk => hcenter jk.1 jk.2) hD hT
    (fun jk => hover jk.1 jk.2) (fun jk => henv jk.1 jk.2) hbudget'
  rw [Fintype.sum_prod_type] at henergy
  have h := hlocal N κ (fun j k => packetSynthesis (c j k) (f j k))
    (u + r * offset) r q (Icc (u - r) (u + r)) (((1 + |offset|) ^ 2 / 8) ^ q)
    (fun j k ξ hξ => packetSynthesis_fourier_zero _ _ ξ (fun i => hlow j k i ξ hξ))
    (fun j k ξ hξ => packetSynthesis_fourier_zero _ _ ξ (fun i => hhigh j k i ξ hξ))
    measurableSet_Icc (box_polynomial_weight_pos offset q).le
    (fun x hx => box_polynomial_weight u r offset x q hr
      (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩))
  exact h.trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal henergy) _)

end LipschitzHilbert

end

end OAI
