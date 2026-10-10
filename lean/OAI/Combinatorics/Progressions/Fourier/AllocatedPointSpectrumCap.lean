import OAI.Combinatorics.Progressions.Probability.AllocatedPhysicalPointMixture

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (j : Fin m) (i : Fin (n j))

variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)

local notation "sources" => allocatedActiveResidueSources B U basis S j i hactive q hq r hsize
local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "torus" => blockTorusFactor (Fintype.card α) (j.val + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)

theorem allocatedActiveResiduePointApproximation_norm_le
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {M : ℕ} [NeZero M] (hM : M = torus * basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (shift z : rows → ℤ) (F : Finset (rows → Fin M)) :
    ‖allocatedActiveResiduePointApproximation B U basis hR S q r j i hactive hq hsize
      M rows shift z F‖ ≤
      positiveModerateSpectrumCardBudget j.val rows.card ((layerTailDegree m + 1) * rows.card)
        P ((torus : ℝ) / (2 * gamma)) ((torus : ℝ) ^ rows.card) 1 + 1 := by
  have hMK : (M : ℝ) ≤ (torus : ℝ) * basisAxisScale (basis j) i := by
    simp only [hM, Nat.cast_mul, le_refl]
  have hscale : ((basisAxisScale (basis j) i : ℝ) / M) ^ rows.card ≤ 1 := by
    rw [hM, Nat.cast_mul]
    exact grid_scale_factor_le_one _ _ _ (blockTorusFactor_pos _ _ _ _)
      (basisAxisScale_pos (basis j) i)
  have hcap := allocatedSupportedResidueSpectrum_absolute_cap B U basis hR S j i hactive q hq r hsize
    hgrid A hA P hcP hsP (Nat.cast_nonneg torus) (Nat.pos_of_ne_zero (NeZero.ne M))
    hMK rows hrows hB
  have hnorm := weightedModerateGridApproximation_norm_le_cap
    (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources (basisAxisScale (basis j) i) M rows
    (fun _ => 0) shift z F hscale (by simpa only [Int.cast_zero] using hcap)
  unfold allocatedActiveResiduePointApproximation
  split_ifs
  · exact hnorm
  · simpa only [norm_zero] using (norm_nonneg _).trans hnorm

theorem allocatedSupportedPointApproximation_norm_le
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {M : ℕ} [NeZero M] (hM : M = torus * basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (ε : ℝ) (shift z : rows → ℤ) :
    ‖allocatedSupportedPointApproximation B U basis hR S q r j i hactive hq hsize
      P ε M rows shift z‖ ≤
      positiveModerateSpectrumCardBudget j.val rows.card ((layerTailDegree m + 1) * rows.card)
        P ((torus : ℝ) / (2 * gamma)) ((torus : ℝ) ^ rows.card) 1 + 1 := by
  unfold allocatedSupportedPointApproximation
  exact allocatedActiveResiduePointApproximation_norm_le B U basis hR S q r j i hactive hq hsize
    hgrid A hA P hcP hsP hM rows hrows hB shift z _

theorem allocatedSupportedPhysicalPointApproximation_norm_le
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {M : ℕ} [NeZero M] (hM : M = torus * basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (ε : ℝ) (z : rows → ℤ) :
    ‖allocatedSupportedPhysicalPointApproximation B U basis hR hσ S q r j i hactive hq hsize
      P ε M rows z‖ ≤
      positiveModerateSpectrumCardBudget j.val rows.card ((layerTailDegree m + 1) * rows.card)
        P ((torus : ℝ) / (2 * gamma)) ((torus : ℝ) ^ rows.card) 1 + 1 := by
  unfold allocatedSupportedPhysicalPointApproximation
  apply pmf_complex_average_norm_le
  intro c
  exact allocatedSupportedPointApproximation_norm_le B U basis hR S q r j i hactive hq hsize
    hgrid A hA P hcP hsP hM rows hrows hB ε _ z

end Erdos3.VectorPolynomial

end

end OAI
