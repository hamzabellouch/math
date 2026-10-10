import OAI.Analysis.LipschitzHilbert.Packets.ParityPackets

namespace OAI

/-! The manuscript's dyadic annular variation estimate, obtained from
the two radix-four subfamilies with exact partial-sum indexing. -/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert

theorem finiteCubicVariation_parity {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (x : ℝ) :
    (finiteCubicVariation (fun i => partialBandSum f i x) N) ^ (2 / 3 : ℝ) ≤
      2 * (finiteCubicVariation (fun i => partialBandSum (parityPacket f 0) i x) N) ^ (2 / 3 : ℝ) +
      2 * (finiteCubicVariation (fun i => partialBandSum (parityPacket f 1) i x) N) ^ (2 / 3 : ℝ) := by
  let E := fun i => partialBandSum (parityPacket f 0) i x
  let O := fun i => partialBandSum (parityPacket f 1) i x
  have heq := finiteCubicVariation_congr (fun i => partialBandSum f i x)
    (fun i => E ((i + 1) / 2) + O (i / 2)) N (fun i hi => partialBandSum_parity f hi x)
  rw [heq]
  have hE := finiteCubicVariation_comp_le E N (fun i => (i + 1) / 2)
    (fun i j hij => Nat.div_le_div_right (Nat.add_le_add_right hij 1)) (by omega)
  have hO := finiteCubicVariation_comp_le O N (fun i => i / 2)
    (fun _ _ hij => Nat.div_le_div_right hij) (by omega)
  have hsum := finiteCubicVariation_add_square (fun i => E ((i + 1) / 2)) (fun i => O (i / 2)) N
  exact hsum.trans (add_le_add
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (finiteCubicVariation_nonneg _ _) hE (by norm_num)) (by norm_num))
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (finiteCubicVariation_nonneg _ _) hO (by norm_num)) (by norm_num)))

theorem lintegral_variation_parity {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) :
    (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun i => partialBandSum f i x) N) ^ (2 / 3 : ℝ)) ≤
      2 * (∫⁻ x, ENNReal.ofReal (finiteCubicVariation
        (fun i => partialBandSum (parityPacket f 0) i x) N) ^ (2 / 3 : ℝ)) +
      2 * (∫⁻ x, ENNReal.ofReal (finiteCubicVariation
        (fun i => partialBandSum (parityPacket f 1) i x) N) ^ (2 / 3 : ℝ)) := by
  have hpoint (x : ℝ) := ENNReal.ofReal_le_ofReal (finiteCubicVariation_parity f x)
  have hpos (g : Fin N → SchwartzMap ℝ ℂ) (x : ℝ) :
      0 ≤ 2 * (finiteCubicVariation (fun i => partialBandSum g i x) N) ^ (2 / 3 : ℝ) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (finiteCubicVariation_nonneg _ _) _)
  simp only [ENNReal.ofReal_add (hpos _ _) (hpos _ _),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _) (by norm_num : (0 : ℝ) ≤ 2 / 3)] at hpoint
  have h := lintegral_mono (μ := volume) hpoint
  have hm (r : ℕ) : Measurable (fun x => ENNReal.ofReal (finiteCubicVariation
      (fun i => partialBandSum (parityPacket f r) i x) N) ^ (2 / 3 : ℝ)) :=
    (measurable_finiteCubicVariation _
      (partialBandSum_measurable (parityPacket f r)) N).ennreal_ofReal.pow_const _
  rw [lintegral_add_left ((hm 0).const_mul (2 : ℝ≥0∞)),
    lintegral_const_mul _ (hm 0), lintegral_const_mul _ (hm 1)] at h
  exact h

theorem dyadic_scalar_annular_variation (hL : LepingleInput) {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (N : ℕ) (f : Fin N → SchwartzMap ℝ ℂ),
      (∀ j ξ, |ξ| < a * (2 : ℝ) ^ j.val → 𝓕 (f j) ξ = 0) →
      (∀ j ξ, b * (2 : ℝ) ^ j.val < |ξ| → 𝓕 (f j) ξ = 0) →
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun i => partialBandSum f i x) N) ^
        (2 / 3 : ℝ)) ≤ (K : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2) := by
  obtain ⟨K0,hK0,h0⟩ := general_scalar_annular_variation hL ha hb
  obtain ⟨K1,hK1,h1⟩ := general_scalar_annular_variation hL
    (mul_pos ha (by norm_num : (0 : ℝ) < 2)) (mul_nonneg hb (by norm_num : (0 : ℝ) ≤ 2))
  refine ⟨2 * K0 + 2 * K1, by positivity, ?_⟩
  intro N f hlow hhigh
  have he := h0 N (parityPacket f 0)
    (by simpa using parityPacket_low f a 0 hlow)
    (by simpa using parityPacket_high f b 0 hhigh)
  have ho := h1 N (parityPacket f 1)
    (by simpa using parityPacket_low f a 1 hlow)
    (by simpa using parityPacket_high f b 1 hhigh)
  have heE := ENNReal.ofReal_le_ofReal (parityPacket_energy f 0)
  have hoE := ENNReal.ofReal_le_ofReal (parityPacket_energy f 1)
  calc
    _ ≤ 2 * ((K0 : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2)) +
        2 * ((K1 : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2)) :=
      (lintegral_variation_parity f).trans (add_le_add
        (mul_le_mul_right (he.trans (mul_le_mul_right heE _)) _)
        (mul_le_mul_right (ho.trans (mul_le_mul_right hoE _)) _))
    _ = _ := by push_cast; ring

theorem dyadic_hilbert_annular_variation (hL : LepingleInput) {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (f : Fin N → κ → SchwartzMap ℝ ℂ),
      (∀ j k ξ, |ξ| < a * (2 : ℝ) ^ j.val → 𝓕 (f j k) ξ = 0) →
      (∀ j k ξ, b * (2 : ℝ) ^ j.val < |ξ| → 𝓕 (f j k) ξ = 0) →
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation
        (fun i => hilbertPartialBandSum f i x) N) ^ (2 / 3 : ℝ)) ≤
      (K : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∑ k, ∫ x, ‖f j k x‖ ^ 2) := by
  obtain ⟨K,hK,hbound⟩ := dyadic_scalar_annular_variation hL ha hb
  refine ⟨K,hK,?_⟩
  intro N κ inst f hlow hhigh
  calc
    _ ≤ ∫⁻ x, ∑ k, ENNReal.ofReal (finiteCubicVariation
        (fun i => partialBandSum (fun j => f j k) i x) N) ^ (2 / 3 : ℝ) := by
      apply lintegral_mono
      intro x
      exact ennreal_complex_variation_coordinates (fun i => hilbertPartialBandSum f i x) N
    _ = ∑ k, ∫⁻ x, ENNReal.ofReal (finiteCubicVariation
        (fun i => partialBandSum (fun j => f j k) i x) N) ^ (2 / 3 : ℝ) := by
      apply lintegral_finsetSum
      intro k _
      exact (measurable_finiteCubicVariation _ (partialBandSum_measurable (fun j => f j k)) N).ennreal_ofReal.pow_const _
    _ ≤ ∑ k, (K : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∫ x, ‖f j k x‖ ^ 2) :=
      Finset.sum_le_sum (fun k _ => hbound N (fun j => f j k)
        (fun j => hlow j k) (fun j => hhigh j k))
    _ = _ := by
      rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg]
      · congr 2
        exact Finset.sum_comm
      · intro k _
        exact Finset.sum_nonneg (fun j _ => integral_nonneg (fun x => sq_nonneg _))

end LipschitzHilbert

end

end OAI
