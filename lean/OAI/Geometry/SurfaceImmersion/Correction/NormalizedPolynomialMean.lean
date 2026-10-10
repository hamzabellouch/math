import OAI.Geometry.SurfaceImmersion.Correction.SupportedPolynomialMeanDifference

namespace OAI

/-! The polynomial part of the normalized quadratic mean is O(η), with
finite-loss value and difference bounds and constants chosen before scales. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

def normalizedPolynomialMean {n : ℕ} (P : Fin n → Expression) (δ ε : ℝ)
    (G : Base → Space) (φ : Base → ℝ) (H : Base → Fin 4 → ℂ) (τ t : ℝ) : Base → ℝ :=
  fun p => δ⁻¹ ^ 2 * quadraticMeanCoefficient P ε G φ H τ t p

lemma normalized_product_scale {δ τ s ε E A D : ℝ} {r p : ℕ}
    (hδ : 0 < δ) (hτ : 0 < τ) (hs : 0 < s) (hτ1 : τ ≤ 1)
    (hε : 0 ≤ ε) (hE : 0 ≤ E) (hA : 0 ≤ A) (hD : 0 ≤ D) (hp : r ≤ p) :
    δ⁻¹ ^ 2 * (E * ε * (A * (δ * τ)) * (D * (δ * τ)) / τ ^ r) ≤
      (τ / s + ε / τ ^ p) * E * A * D := by
  have hfrac : ε / τ ^ r ≤ ε / τ ^ p :=
    div_le_div_of_nonneg_left hε (pow_pos hτ p) (pow_le_pow_of_le_one hτ.le hτ1 hp)
  have hsmall : ε * τ ^ 2 / τ ^ r ≤ τ / s + ε / τ ^ p := by
    calc
      _ = (ε / τ ^ r) * τ ^ 2 := by ring
      _ ≤ ε / τ ^ r := mul_le_of_le_one_right (div_nonneg hε (pow_nonneg hτ.le _))
        (pow_le_one₀ hτ.le hτ1)
      _ ≤ ε / τ ^ p := hfrac
      _ ≤ _ := le_add_of_nonneg_left (div_nonneg hτ.le hs.le)
  calc
    _ = (ε * τ ^ 2 / τ ^ r) * (E * A * D) := by
      field_simp [hδ.ne']
    _ ≤ (τ / s + ε / τ ^ p) * (E * A * D) :=
      mul_le_mul_of_nonneg_right hsmall (mul_nonneg (mul_nonneg hE hA) hD)
    _ = _ := by ring

theorem normalizedPolynomialMean_bounds {n : ℕ} {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O)
    (m : ℕ) (B F : ℝ) (hB : 1 ≤ B) (hF : 0 ≤ F) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (φ : Base → ℝ)
      (_hG : ContDiff ℝ ∞ G) (_hφ : ContDiff ℝ ∞ φ) (K : Compacts Base)
      (H J : SupportedField (F := Fin 4 → ℂ) K) (s : ℝ≥0) (δ τ ε A D : ℝ) (p : ℕ),
      0 < δ → 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → 0 ≤ A → 0 ≤ D → loss P ≤ p →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + order P) B (lowJet G) →
      (∀ v, WeightedBound U s (m + order P) F (fun p => fderiv ℝ φ p (coordinateVector v))) →
      supportedWeightedSeminorm K s (m + order P) H ≤ A * (δ * τ) →
      supportedWeightedSeminorm K s (m + order P) J ≤ A * (δ * τ) →
      supportedWeightedSeminorm K s (m + order P) (H - J) ≤ D * (δ * τ) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m ((τ / s + ε / τ ^ p) * E * A ^ 2)
          (normalizedPolynomialMean P δ ε G φ H τ t) ∧
        WeightedBound U s m ((τ / s + ε / τ ^ p) * (2 * E) * A * D)
          (fun x => normalizedPolynomialMean P δ ε G φ H τ t x -
            normalizedPolynomialMean P δ ε G φ J τ t x) := by
  obtain ⟨Ev, hEv, hv⟩ := supported_quadraticMeanPair_bound hU hO hQ hQO P hP m B F hB hF
  obtain ⟨Ed, hEd, hd⟩ := supported_quadraticMean_difference hU hO hQ hQO P hP m B F hB hF
  let E := max Ev Ed
  have hE : 0 ≤ E := hEv.trans (le_max_left _ _)
  refine ⟨E, hE, ?_⟩
  intro G φ hG hφ K H J s δ τ ε A D p hδ hτ hs hτs hs1 hε hε1 hA hD hp hGQ hGb hφb hH hJ hHJ t ht
  have hτ1 : τ ≤ 1 := hτs.trans hs1
  have hη : 0 ≤ τ / s + ε / τ ^ p :=
    add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  have hsH := quadraticMeanCoefficient_smooth hO hP hG hφ H.contDiff
    (fun _ hx => hQO (hGQ hx)) ε τ t
  have hsJ := quadraticMeanCoefficient_smooth hO hP hG hφ J.contDiff
    (fun _ hx => hQO (hGQ hx)) ε τ t
  constructor
  · have hh := hv G φ hG hφ K H H s τ ε hτ hs hτs hs1 hε hε1 hGQ hGb hφb t ht
    have hb := hh.mono_const (show Ev * ε * supportedWeightedSeminorm K s _ H *
        supportedWeightedSeminorm K s _ H / τ ^ loss P ≤
        Ev * ε * (A * (δ * τ)) * (A * (δ * τ)) / τ ^ loss P by gcongr)
    have heq : quadraticMeanPair P ε G φ H H τ t = quadraticMeanCoefficient P ε G φ H τ t := by
      funext x
      exact quadraticMeanPair_self P ε G hφ H.contDiff τ t x
    rw [heq] at hb
    have hscaled := hb.const_smul hU.uniqueDiffOn hsH (δ⁻¹ ^ 2)
    change WeightedBound U s m _ (normalizedPolynomialMean P δ ε G φ H τ t) at hscaled
    rw [abs_of_nonneg (sq_nonneg δ⁻¹)] at hscaled
    apply hscaled.mono_const
    calc
      _ ≤ (τ / s + ε / τ ^ p) * Ev * A * A :=
        normalized_product_scale hδ hτ hs hτ1 hε hEv hA hA hp
      _ ≤ (τ / s + ε / τ ^ p) * E * A * A := by gcongr; exact le_max_left _ _
      _ = _ := by ring
  · have hh := hd G φ hG hφ K H J s τ ε (A * (δ * τ)) (D * (δ * τ))
      hτ hs hτs hs1 hε hε1 (by positivity) (by positivity) hGQ hGb hφb hH hJ hHJ t ht
    have hscaled := hh.const_smul hU.uniqueDiffOn (hsH.sub hsJ) (δ⁻¹ ^ 2)
    have heq : (fun x => δ⁻¹ ^ 2 • (quadraticMeanCoefficient P ε G φ H τ t x -
        quadraticMeanCoefficient P ε G φ J τ t x)) =
        fun x => normalizedPolynomialMean P δ ε G φ H τ t x -
          normalizedPolynomialMean P δ ε G φ J τ t x := by
      funext x
      simp only [normalizedPolynomialMean, smul_eq_mul, mul_sub]
    rw [heq, abs_of_nonneg (sq_nonneg δ⁻¹)] at hscaled
    apply hscaled.mono_const
    calc
      _ ≤ (τ / s + ε / τ ^ p) * (2 * Ed) * A * D :=
        normalized_product_scale hδ hτ hs hτ1 hε (by positivity) hA hD hp
      _ ≤ _ := by gcongr; exact le_max_right _ _

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
