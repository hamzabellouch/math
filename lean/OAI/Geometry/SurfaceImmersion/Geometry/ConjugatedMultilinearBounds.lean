import OAI.Geometry.SurfaceImmersion.Geometry.ModulatedJetScaling

namespace OAI

/-! The conjugated polynomial estimates retain the product of the input
amplitude bounds. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates MixedExpression

/-- Product estimate corresponding to the fixed-power perturbation bound
in the small-modes argument. No output-order or accuracy dependence is
hidden in the short-scale exponent. -/
theorem compact_conjugated_multilinear_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : Expression) (he : e.SmoothCoeffs O) (m : ℕ) (B P : ℝ) (hB : 1 ≤ B) (hP : 0 ≤ P) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (φ : Fin 3 → Base → ℝ)
      (H : DirectionFields) (s τ : ℝ) (C : Fin 3 → ℝ),
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 → (∀ j, 0 < C j) →
      ContDiff ℝ ∞ G → (∀ j, ContDiff ℝ ∞ (φ j)) → (∀ j, ContDiff ℝ ∞ (H j)) →
      Set.MapsTo (lowJet G) U K →
      WeightedBound U s (m + e.order) B (lowJet G) →
      (∀ j, WeightedBound U s (m + e.order) (C j) (H j)) →
      (∀ j v, WeightedBound U s (m + e.order) P
        (fun p => fderiv ℝ (φ j) p (coordinateVector v))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin 3,
        WeightedBound U s m
          (D * (C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)) /
            τ ^ (e.loss + 6)) (fun p => conjugatedVariation e G φ H τ i (p, t)) := by
  obtain ⟨D, hD, hb⟩ := compact_conjugated_variation_bound hU hO hK hKO e he m B P hB hP
  refine ⟨D, hD, ?_⟩
  intro G φ H s τ C hτ hs hτs hs1 hC hG hφ hH hGK hGb hHb hφb t ht i
  let V := scaleDirections H (fun j => (C j)⁻¹)
  have hV := scaleDirections_smooth hH (fun j => (C j)⁻¹)
  have hunit : ∀ j, WeightedBound U s (m + e.order) 1 (V j) := by
    intro j
    have h := (hHb j).const_smul hU.uniqueDiffOn (hH j).contDiffOn (C j)⁻¹
    change WeightedBound U s (m + e.order) 1 (fun p => (C j)⁻¹ • H j p)
    simpa only [abs_of_pos (inv_pos.mpr (hC j)),
      inv_mul_cancel₀ (ne_of_gt (hC j))] using h
  have hbound := hb G φ V s τ hτ hs hτs hs1 hG hφ hV hGK hGb hunit hφb t ht i
  let W : ℝ := C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)
  have hW : 0 < W := by
    have h₀ := hC 0
    have h₁ := hC 1
    have h₂ := hC 2
    dsimp only [W]
    split_ifs <;> positivity
  have heq : (fun p => conjugatedVariation e G φ H τ i (p, t)) =
      (fun p => W • conjugatedVariation e G φ V τ i (p, t)) := by
    funext p
    have h := conjugatedVariation_scale e G hφ hV τ C i (p, t)
    rw [scaleDirections_inverse H C (fun j => ne_of_gt (hC j))] at h
    exact h
  rw [heq]
  have hsmooth : ContDiffOn ℝ ∞ (fun p => conjugatedVariation e G φ V τ i (p, t)) U := by
    have h := evalComplex_parameter_smooth hG (fun p hp => hKO (hGK hp))
      (fun j w a => (amplitudeData_smooth hG hφ hV τ j w a).contDiffOn)
      (e := e.variations i) (e.variations_smoothCoeffs hO he i) t
    convert h using 1
    funext p
    exact conjugatedVariation_eq e G hφ hV τ i (p, t)
  have h := hbound.const_smul hU.uniqueDiffOn hsmooth W
  convert h using 1
  rw [abs_of_pos hW]
  ring

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
