import OAI.Geometry.SurfaceImmersion.Correction.SupportedPolynomialMean

namespace OAI

/-! The finite-loss difference estimate for the actual polynomial mean. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma quadraticMeanPair_smooth {n : ℕ} {P : Fin n → Expression}
    {U : Set Base} {O : Set LowJet} (hO : IsOpen O) (hP : ∀ l, (P l).SmoothCoeffs O)
    {G : Base → Space} {φ : Base → ℝ} {H J : Base → Fin 4 → ℂ}
    (hG : ContDiff ℝ ∞ G) (hφ : ContDiff ℝ ∞ φ)
    (hH : ContDiff ℝ ∞ H) (hJ : ContDiff ℝ ∞ J)
    (hQ : Set.MapsTo (lowJet G) U O) (ε τ t : ℝ) :
    ContDiffOn ℝ ∞ (quadraticMeanPair P ε G φ H J τ t) U := by
  have hs := fun l => conjugatedVariation_smooth (hP l) hG (pairPhases_smooth hφ hφ.neg)
    (pairDirections_smooth hH (starField_smooth hJ)) hO hQ τ 1 t
  have hh : ContDiffOn ℝ ∞ (fun p =>
      (conjugated P ε G (pairPhases φ (fun p => -φ p))
        (pairDirections H (starField J)) τ 1 (p, t)).re / 4) U :=
    (Complex.reCLM.contDiff.comp_contDiffOn
    (ContDiffOn.sum fun l _ => (hs l).const_smul (ε ^ (l.val + 1)))).div_const 4
  have he : quadraticMeanPair P ε G φ H J τ t =
      fun p => (conjugated P ε G (pairPhases φ (fun p => -φ p))
        (pairDirections H (starField J)) τ 1 (p, t)).re / 4 := by
    funext p
    exact quadraticMeanPair_eq P ε G hφ H hJ τ t p
  rw [he]
  exact hh

theorem supported_quadraticMean_difference {n : ℕ} {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O)
    (m : ℕ) (B F : ℝ) (hB : 1 ≤ B) (hF : 0 ≤ F) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (φ : Base → ℝ)
      (_hG : ContDiff ℝ ∞ G) (_hφ : ContDiff ℝ ∞ φ) (K : Compacts Base)
      (H J : SupportedField (F := Fin 4 → ℂ) K) (s : ℝ≥0) (τ ε A D : ℝ),
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 ≤ A → 0 ≤ D →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + order P) B (lowJet G) →
      (∀ v, WeightedBound U s (m + order P) F (fun p => fderiv ℝ φ p (coordinateVector v))) →
      supportedWeightedSeminorm K s (m + order P) H ≤ A →
      supportedWeightedSeminorm K s (m + order P) J ≤ A →
      supportedWeightedSeminorm K s (m + order P) (H - J) ≤ D →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (2 * E * ε * A * D / τ ^ loss P)
          (fun p => quadraticMeanCoefficient P ε G φ H τ t p -
            quadraticMeanCoefficient P ε G φ J τ t p) := by
  obtain ⟨E, hE, he⟩ := supported_quadraticMeanPair_bound hU hO hQ hQO P hP m B F hB hF
  refine ⟨E, hE, ?_⟩
  intro G φ hG hφ K H J s τ ε A D hτ hs hτs hs1 hε hε1 hA hD hGQ hGb hφb hH hJ hHJ t ht
  have h1 := he G φ hG hφ K (H - J) H s τ ε hτ hs hτs hs1 hε hε1 hGQ hGb hφb t ht
  have h2 := he G φ hG hφ K J (H - J) s τ ε hτ hs hτs hs1 hε hε1 hGQ hGb hφb t ht
  have h1' := h1.mono_const (show E * ε * supportedWeightedSeminorm K s _ (H - J) *
      supportedWeightedSeminorm K s _ H / τ ^ loss P ≤ E * ε * D * A / τ ^ loss P by gcongr)
  have h2' := h2.mono_const (show E * ε * supportedWeightedSeminorm K s _ J *
      supportedWeightedSeminorm K s _ (H - J) / τ ^ loss P ≤ E * ε * A * D / τ ^ loss P by gcongr)
  have hHQ : Set.MapsTo (lowJet G) U O := fun _ hx => hQO (hGQ hx)
  have hadd := h1'.add hU.uniqueDiffOn hs.le
    (quadraticMeanPair_smooth hO hP hG hφ (H - J).contDiff H.contDiff hHQ ε τ t)
    (quadraticMeanPair_smooth hO hP hG hφ J.contDiff (H - J).contDiff hHQ ε τ t) h2'
  have hfinal := hadd.congr (fun x _ =>
    quadraticMeanCoefficient_difference P ε G hφ (H := H) (K := J) H.contDiff J.contDiff τ t x)
  convert hfinal using 1
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
