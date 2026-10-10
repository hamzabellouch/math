import OAI.Geometry.SurfaceImmersion.Geometry.ModulatedJetDataBounds

namespace OAI

/-! Sharp slow-scale estimates for the first three conjugated polynomial
variations. The power E+6 is independent of correction accuracy and order. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates MixedExpression

def phaseProduct (φ : Fin 3 → Base → ℝ) (τ : ℝ) (i : Fin 3) (p : Base) : ℂ :=
  phase τ (φ 0) p * (if 1 ≤ i then phase τ (φ 1) p else 1) *
    (if 2 ≤ i then phase τ (φ 2) p else 1)

lemma phaseProduct_ne_zero (φ : Fin 3 → Base → ℝ) (τ : ℝ) (i : Fin 3) (p : Base) :
    phaseProduct φ τ i p ≠ 0 := by
  have h (j : Fin 3) : phase τ (φ j) p ≠ 0 := Complex.exp_ne_zero _
  apply mul_ne_zero
  · exact mul_ne_zero (h 0) (by split_ifs; exact h 1; exact one_ne_zero)
  · split_ifs
    · exact h 2
    · exact one_ne_zero

def conjugatedVariation (e : Expression) (G : Base → Space)
    (φ : Fin 3 → Base → ℝ) (H : DirectionFields) (τ : ℝ) (i : Fin 3) (z : Base × ℝ) : ℂ :=
  (phaseProduct φ τ i z.1)⁻¹ * (e.variations i).evalComplex G (oscillatoryData G φ H τ) z

lemma conjugatedVariation_eq (e : Expression) (G : Base → Space) {φ : Fin 3 → Base → ℝ}
    {H : DirectionFields} (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (hH : ∀ j, ContDiff ℝ ∞ (H j)) (τ : ℝ) (i : Fin 3) (z : Base × ℝ) :
    conjugatedVariation e G φ H τ i z =
      (e.variations i).evalComplex G (amplitudeData G φ H τ) z := by
  rw [conjugatedVariation, variation_phase_factor e G hφ hH τ z i]
  change (phaseProduct φ τ i z.1)⁻¹ *
    (phaseProduct φ τ i z.1 * (e.variations i).evalComplex G (amplitudeData G φ H τ) z) = _
  rw [← mul_assoc, inv_mul_cancel₀ (phaseProduct_ne_zero φ τ i z.1), one_mul]

/-- Unit amplitude bounds give the sharp exponent for every first, second,
and third variation after removing all participating phase factors. -/
theorem compact_conjugated_variation_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : Expression) (he : e.SmoothCoeffs O) (m : ℕ) (B P : ℝ) (hB : 1 ≤ B) (hP : 0 ≤ P) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (φ : Fin 3 → Base → ℝ)
      (H : DirectionFields) (s τ : ℝ),
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 →
      ContDiff ℝ ∞ G → (∀ j, ContDiff ℝ ∞ (φ j)) → (∀ j, ContDiff ℝ ∞ (H j)) →
      Set.MapsTo (lowJet G) U K →
      WeightedBound U s (m + e.order) B (lowJet G) →
      (∀ j, WeightedBound U s (m + e.order) 1 (H j)) →
      (∀ j v, WeightedBound U s (m + e.order) P
        (fun p => fderiv ℝ (φ j) p (coordinateVector v))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin 3,
        WeightedBound U s m (D / τ ^ (e.loss + 6))
          (fun p => conjugatedVariation e G φ H τ i (p, t)) := by
  classical
  let A := amplitudeBudget e.order m B P
  have hA : 1 ≤ A := amplitudeBudget_ge_one (zero_le_one.trans hB) hP
  have hex := fun i : Fin 3 => compact_complex_mixed_bound hU hO hK hKO (e.variations i)
    (e.variations_smoothCoeffs hO he i) m A hA
  choose D hD hb using hex
  refine ⟨∑ i, D i, Finset.sum_nonneg (fun i _ => hD i), ?_⟩
  intro G φ H s τ hτ hs hτs hs1 hG hφ hH hGK hGb hHb hφb t ht i
  have hdata := weighted_amplitudeData hU hG hφ hH hτ hs hτs (zero_le_one.trans hB) hP
    m e.order hGb hHb hφb
  have h := hb i G (amplitudeData G φ H τ) s τ hs hτ (hτs.trans hs1) hG hGK
    ((hGb.mono_order (by omega)).mono_const (le_amplitudeBudget hP))
    (fun j w a => (amplitudeData_smooth hG hφ hH τ j w a).contDiffOn)
    (fun j w a hw => hdata j w a (hw.trans (e.variations_order i))) t ht
  have hbound : D i / τ ^ (e.variations i).loss ≤ (∑ j, D j) / τ ^ (e.loss + 6) := by
    calc
      _ ≤ D i / τ ^ (e.loss + 6) := div_le_div_of_nonneg_left (hD i) (pow_pos hτ _)
        (pow_le_pow_of_le_one hτ.le (hτs.trans hs1) (e.variations_loss i))
      _ ≤ _ := div_le_div_of_nonneg_right
        (Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ i)) (pow_nonneg hτ.le _)
  apply (h.mono_const hbound).congr
  intro p _
  exact conjugatedVariation_eq e G hφ hH τ i (p, t)

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
