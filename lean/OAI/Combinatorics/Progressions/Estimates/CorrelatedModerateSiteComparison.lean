import OAI.Combinatorics.Progressions.Fourier.CorrelatedModerateFourierShift

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem exists_correlatedModerate_pointMass_sites
    {B I Cell : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
    {n K M : ℕ} [NeZero M]
    (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin n → NormalizedScalarCubeSource I)
    (aCell : Cell → (∀ b, IntegerScalarCubeBox Empty (c b).length) → ℂ)
    (ha : ∀ cell z, ‖aCell cell z‖ ≤ 1) (offset : B → ℤ)
    {A : ℝ} (hA : 0 ≤ A) (hK : 0 < K)
    (hvol : ∀ b, (|(offset b : ℝ)| + (c b).length) *
      (∏ v, ((s b v).length : ℝ)) ≤ A * K)
    (hM : M = blockTorusFactor (Fintype.card I) n (Fintype.card B) A * K)
    (rows : Finset (Finset I)) (hrows : ∀ t ∈ rows, t.card ≤ n)
    (shift : rows → ℤ) (F : Finset (rows → Fin M))
    {ε : ℝ} (hε : 0 ≤ ε)
    (htail : ∀ cell, spectrumTail F (fun k =>
      ‖correlatedModerateFourierCoefficient c s (aCell cell) offset M rows shift k‖) ≤ ε)
    (D : F → ℕ) [∀ k, NeZero (D k)]
    (rationalFrequency : F → rows → ℤ) (ω : F → rows → ℝ)
    (hfreq : ∀ k t, (((k.val t).val : ℝ) / M) =
      (rationalFrequency k t : ℝ) / D k + ω k t / K)
    {C : ℝ} (hcard : (F.card : ℝ) ≤ C)
    (W : ℝ≥0) (hW : ∀ k t, |ω k t| ≤ W)
    {R δ P : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hP : 0 ≤ P)
    (hRP : R ≤ Real.exp P) (hδP : (δ / (C + 1))⁻¹ ≤ Real.exp P)
    (hLP : ((CircleFourier.characterLipConstant * (rows.card * W) + 4) *
      (2 : ℝ≥0) ^ Fintype.card I : ℝ≥0) ≤ Real.exp P) :
    ∃ count : F → ℕ, (∀ k, (count k : ℝ) ≤ Real.exp (4 * P + 8)) ∧
      (Fintype.card (PlateauSiteIndex I F count) : ℝ) ≤
        F.card * Real.exp (Fintype.card (Finset I) * (4 * P + 8)) ∧
      ∃ (coeff : Cell → PlateauSiteIndex I F count → ℂ)
        (factor : (k : PlateauSiteIndex I F count) → Finset I → ZMod (D k.1) → ℝ → ℂ),
        (∀ cell, (∑ k, ‖coeff cell k‖) ≤ C *
          Real.exp (Fintype.card (Finset I) * (4 * P + 8) + P)) ∧
        (∀ k u r x, ‖factor k u r x‖ ≤ 1) ∧
        (∀ k u r, LipschitzWith ⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩
          (factor k u r)) ∧
        ∀ cell (y : Finset I → ℤ), (∀ u, |(y u : ℝ) / K| ≤ R) →
          ‖(K : ℂ) ^ rows.card * correlatedModeratePointMass c s (aCell cell)
              rows offset shift (fun t => booleanCoefficient y t) -
            ∑ k, coeff cell k * ∏ u, factor k u (y u : ZMod (D k.1))
              ((y u : ℝ) / K)‖ ≤ ε + δ := by
  let β : Cell → F → ℂ := fun cell k =>
    correlatedModerateFourierCoefficient c s (aCell cell) offset M rows 0 k.val
  have hC : 0 ≤ C := (Nat.cast_nonneg F.card).trans hcard
  have hcap (cell : Cell) : (∑ k, ‖β cell k‖) ≤ C :=
    (correlatedModerateFourierCoefficient_retained_mass c s (aCell cell) offset
      (ha cell) rows 0 F).trans hcard
  have hscale : ((K : ℝ) / M) ^ rows.card ≤ 1 := by
    rw [hM, Nat.cast_mul]
    exact grid_scale_factor_le_one _ K rows.card (blockTorusFactor_pos _ _ _ _) hK
  let H := blockJetScaleBound (Fintype.card I) n (Fintype.card B) A
  obtain ⟨count, hcount, hterms, coeff, factor, hcoeff, hfactor, hLip, herr⟩ :=
    exists_forecastModerate_weighted_sites rows F H hK shift D rationalFrequency ω hfreq
      β hC hcap hscale W hW hR hδ hP hRP hδP hLP
  refine ⟨count, hcount, hterms, coeff, factor, hcoeff, hfactor, hLip, ?_⟩
  intro cell y hy
  have hpoint := correlatedModeratePointMass_error_plateau c s (aCell cell) offset hA hK
    hvol hM rows hrows shift (fun t => booleanCoefficient y t) F hε (htail cell)
  have hsite := herr cell y hy
  rw [← correlatedModeratePlateauApproximation_eq_weightedFourierSum c s (aCell cell)
    offset H rows shift (fun t => booleanCoefficient y t) F] at hsite
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hpoint hsite)

end Erdos3

end

end OAI
