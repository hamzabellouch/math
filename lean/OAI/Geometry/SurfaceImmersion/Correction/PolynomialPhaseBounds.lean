import OAI.Geometry.SurfaceImmersion.Correction.PolynomialPhaseSupport

namespace OAI

/-! Uniform product bounds for the actual nonzero-phase coefficients. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates MixedExpression ModulatedJets

theorem quadraticPhaseCoefficient_bound {n : ℕ} {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O)
    (m : ℕ) (B F : ℝ) (hB : 1 ≤ B) (hF : 0 ≤ F) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (φ ψ : Base → ℝ)
      (H K : Base → Fin 4 → ℂ) (s τ ε C D : ℝ),
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < C → 0 < D →
      ContDiff ℝ ∞ G → ContDiff ℝ ∞ φ → ContDiff ℝ ∞ ψ →
      ContDiff ℝ ∞ H → ContDiff ℝ ∞ K →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + order P) B (lowJet G) →
      WeightedBound U s (m + order P) C H → WeightedBound U s (m + order P) D K →
      (∀ v, WeightedBound U s (m + order P) F (fun p => fderiv ℝ φ p (coordinateVector v))) →
      (∀ v, WeightedBound U s (m + order P) F (fun p => fderiv ℝ ψ p (coordinateVector v))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (E * ε * C * D / τ ^ loss P)
          (quadraticPhaseCoefficient P ε G φ ψ H K τ t) := by
  obtain ⟨E, hE, he⟩ := compact_conjugated_bound hU hO hQ hQO P hP m B F hB hF
  refine ⟨E / 4, div_nonneg hE (by norm_num), ?_⟩
  intro G φ ψ H K s τ ε C D hτ hs hτs hs1 hε hε1 hC hD hG hφ hψ hH hK hGQ hGb hHb hKb hφb hψb t ht
  have hpb : ∀ j v, WeightedBound U s (m + order P) F
      (fun p => fderiv ℝ (pairPhases φ ψ j) p (coordinateVector v)) := by
    intro j v
    fin_cases j
    · exact hφb v
    · exact hψb v
    · change WeightedBound U s (m + order P) F
        (fun p => fderiv ℝ (fun _ : Base => (0 : ℝ)) p (coordinateVector v))
      simpa only [fderiv_fun_const, Pi.zero_apply, zero_apply] using
        (weightedBound_zero U s (m + order P)).mono_const hF
  have hhb : ∀ j, WeightedBound U s (m + order P) (![C, D, 1] j) (pairDirections H K j) := by
    intro j
    fin_cases j
    · exact hHb
    · exact hKb
    · exact (weightedBound_zero U s (m + order P)).mono_const zero_le_one
  have hh := he G (pairPhases φ ψ) (pairDirections H K) s τ ε ![C, D, 1]
    hτ hs hτs hs1 hε hε1 (fun j => by fin_cases j; exact hC; exact hD; norm_num)
    hG (pairPhases_smooth hφ hψ) (pairDirections_smooth hH hK) hGQ hGb hhb hpb t ht 1
  have hsm : ContDiffOn ℝ ∞ (fun p => conjugated P ε G
      (pairPhases φ ψ) (pairDirections H K) τ 1 (p,t)) U :=
    ContDiffOn.sum fun l _ =>
      (conjugatedVariation_smooth (hP l) hG (pairPhases_smooth hφ hψ)
        (pairDirections_smooth hH hK) hO (fun _ hp => hQO (hGQ hp)) τ 1 t).const_smul _
  have hf := hh.const_smul hU.uniqueDiffOn hsm (1 / 4 : ℝ)
  convert hf using 1
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, show (1 : Fin 3) ≤ 1 by decide,
      show ¬ (2 : Fin 3) ≤ 1 by decide, ↓reduceIte, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    ring
  · funext p
    simp only [quadraticPhaseCoefficient, Complex.real_smul, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat]
    ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
