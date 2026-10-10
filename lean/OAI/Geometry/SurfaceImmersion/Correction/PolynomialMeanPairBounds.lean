import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMeanDifference

namespace OAI

/-! Product estimates for the two independent amplitudes of the polynomial mean. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates MixedExpression ModulatedJets

lemma quadraticMeanPair_eq {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (H : Base → Fin 4 → ℂ)
    {K : Base → Fin 4 → ℂ} (hK : ContDiff ℝ ∞ K) (τ t : ℝ) (p : Base) :
    quadraticMeanPair P ε G φ H K τ t p =
      (conjugated P ε G (pairPhases φ (fun p => -φ p)) (pairDirections H (starField K)) τ 1 (p, t)).re / 4 := by
  simp only [quadraticMeanPair, quadraticComplex_opposite_phases _ G hφ hK,
    conjugated, Complex.re_sum, Complex.real_smul, Finset.sum_div,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem quadraticMeanPair_bound {n : ℕ} {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O)
    (m : ℕ) (B F : ℝ) (hB : 1 ≤ B) (hF : 0 ≤ F) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (φ : Base → ℝ)
      (H K : Base → Fin 4 → ℂ) (s τ ε C D : ℝ),
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < C → 0 < D →
      ContDiff ℝ ∞ G → ContDiff ℝ ∞ φ → ContDiff ℝ ∞ H → ContDiff ℝ ∞ K →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + order P) B (lowJet G) →
      WeightedBound U s (m + order P) C H → WeightedBound U s (m + order P) D K →
      (∀ v, WeightedBound U s (m + order P) F (fun p => fderiv ℝ φ p (coordinateVector v))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (E * ε * C * D / τ ^ loss P) (quadraticMeanPair P ε G φ H K τ t) := by
  obtain ⟨E, hE, he⟩ := compact_conjugated_bound hU hO hQ hQO P hP m B F hB hF
  refine ⟨E / 4, div_nonneg hE (by norm_num), ?_⟩
  intro G φ H K s τ ε C D hτ hs hτs hs1 hε hε1 hC hD hG hφ hH hK hGQ hGb hHb hKb hφb t ht
  have hpb : ∀ j v, WeightedBound U s (m + order P) F
      (fun p => fderiv ℝ (pairPhases φ (fun p => -φ p) j) p (coordinateVector v)) := by
    intro j v
    fin_cases j
    · exact hφb v
    · have hh := (hφb v).neg hU.uniqueDiffOn
        ((hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).contDiffOn
      change WeightedBound U s (m + order P) F
        (fun p => fderiv ℝ (fun q => -φ q) p (coordinateVector v))
      simpa only [fderiv_fun_neg, neg_apply] using hh
    · change WeightedBound U s (m + order P) F (fun p => fderiv ℝ (fun _ : Base => (0 : ℝ)) p (coordinateVector v))
      simpa only [fderiv_fun_const, Pi.zero_apply, zero_apply] using
        (weightedBound_zero U s (m + order P)).mono_const hF
  have hhb : ∀ j, WeightedBound U s (m + order P) (![C, D, 1] j) (pairDirections H (starField K) j) := by
    intro j
    fin_cases j
    · exact hHb
    · exact weighted_starField hU.uniqueDiffOn hs hD.le hK hKb
    · exact (weightedBound_zero U s (m + order P)).mono_const zero_le_one
  have hh := he G (pairPhases φ (fun p => -φ p)) (pairDirections H (starField K)) s τ ε ![C, D, 1]
    hτ hs hτs hs1 hε hε1 (fun j => by fin_cases j; exact hC; exact hD; norm_num)
    hG (pairPhases_smooth hφ hφ.neg) (pairDirections_smooth hH (starField_smooth hK))
    hGQ hGb hhb hpb t ht 1
  have hsm : ContDiffOn ℝ ∞ (fun p => conjugated P ε G
      (pairPhases φ (fun p => -φ p)) (pairDirections H (starField K)) τ 1 (p, t)) U :=
    ContDiffOn.sum fun l _ =>
      (conjugatedVariation_smooth (hP l) hG (pairPhases_smooth hφ hφ.neg)
        (pairDirections_smooth hH (starField_smooth hK)) hO (fun _ hp => hQO (hGQ hp)) τ 1 t).const_smul _
  have hr := hh.linear hU.uniqueDiffOn hs.le hsm Complex.reCLM
  have hn : 0 ≤ E * ε * (C * D * 1) / τ ^ loss P := by positivity
  have hr' := hr.mono_const (mul_le_of_le_one_left hn (by simp : ‖Complex.reCLM‖ ≤ 1))
  have hf := hr'.const_smul hU.uniqueDiffOn (Complex.reCLM.contDiff.comp_contDiffOn hsm) (1 / 4 : ℝ)
  have hfun : (fun p => (1 / 4 : ℝ) • Complex.reCLM
      (conjugated P ε G (pairPhases φ (fun p => -φ p)) (pairDirections H (starField K)) τ 1 (p, t))) =
      quadraticMeanPair P ε G φ H K τ t := by
    funext p
    rw [quadraticMeanPair_eq P ε G hφ H hK]
    simp only [Complex.reCLM_apply, smul_eq_mul]
    ring
  change WeightedBound U s m _ _ at hf
  rw [Function.comp_def, hfun] at hf
  convert hf using 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, show (1 : Fin 3) ≤ 1 by decide,
    show ¬ (2 : Fin 3) ≤ 1 by decide, ↓reduceIte, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
