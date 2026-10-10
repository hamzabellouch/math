import OAI.Combinatorics.Progressions.Fourier.CorrelatedModerateFourierShift

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hR : ∀ j, 0 < R j)

local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i
local notation "torus" => blockTorusFactor (Fintype.card α) (j.val + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 4

variable (P : ℝ) (rows : Finset (Finset α)) (ε : ℝ)
local notation "tailOrder" => (layerTailDegree m + 2) * rows.card
local notation "tailWeight" => (2 * (torus : ℝ)) ^ rows.card
local notation "bias" => positiveModerateRetainedBias j.val rows.card tailOrder
  P (4 * (torus : ℝ)) tailWeight ε
local notation "cap" => positiveModerateSpectrumCardBudget j.val rows.card tailOrder
  P (4 * (torus : ℝ)) tailWeight ε
local notation "frequencyBound" => positiveRetainedFrequencyBound j.val rows.card
  P (4 * (torus : ℝ)) bias
local notation "denominatorBound" => positiveRetainedDenominatorBound j.val rows.card tailOrder
  P (4 * (torus : ℝ)) tailWeight bias

include hactive hR in
theorem allocatedCorrelatedModerate_retained_modes
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hgamma : gamma ≤ S.value) (hP : 1 ≤ P) (hε : 0 < ε) (hε1 : ε ≤ 1)
    {M : ℕ} (hM : M = torus * scale) :
    let F := positiveModerateSpectrumCover rows M j.val P (4 * (torus : ℝ)) S.value bias
    (F.card : ℝ) ≤ cap ∧
      ∃ (D : F → ℕ) (a : F → rows → ℤ) (ω : F → rows → ℝ),
        (∀ k, 0 < D k ∧ (D k : ℝ) ≤ denominatorBound) ∧
        (∀ k t, |ω k t| ≤ frequencyBound) ∧
        ∀ k t, (((k.val t).val : ℝ) / M) = (a k t : ℝ) / D k + ω k t / scale := by
  let F := positiveModerateSpectrumCover rows M j.val P (4 * (torus : ℝ)) S.value bias
  have hK := allocatedPrincipalGridScale_pos B U basis hR S j i hactive
  have hKM : scale ≤ M := by
    rw [hM]
    exact Nat.le_mul_of_pos_left _ (blockTorusFactor_pos _ _ _ _)
  have hMN : (M : ℝ) ≤ (torus : ℝ) * scale := by
    simp only [hM, Nat.cast_mul, le_refl]
  have hcard := allocatedPrincipalGridScale_cardinality B U basis hR S j i hactive
    hgrid hgamma (Nat.cast_nonneg torus) hMN rows.card
  constructor
  · simpa only [Fintype.card_coe] using
      positiveModerateSpectrumCover_card_budget rows M j.val tailOrder hP
        (by positivity : (0 : ℝ) ≤ 4 * (torus : ℝ))
        (by positivity : (0 : ℝ) ≤ tailWeight) (Nat.cast_nonneg S.value) hε hε1
        (by simpa only [Fintype.card_coe] using hcard)
  · have hex (k : F) := positiveModerateSpectrumCover_character (J := rows)
      hK hKM j.val tailOrder (U := P) (V := 4 * (torus : ℝ)) (ζ := bias)
      (Nat.cast_nonneg S.value) (by positivity : (0 : ℝ) ≤ tailWeight)
      (by simpa only [Fintype.card_coe] using hcard) k.val k.property
    simp only [Fintype.card_coe] at hex
    choose D hD hDb a ω hω heq using hex
    exact ⟨D, a, ω, fun k => ⟨hD k, hDb k⟩, hω, heq⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (q : ℕ) [NeZero q] (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : (Fintype.card α + 1) * q ≤ S.value) (hR : ∀ j, 0 < R j)

local notation "sources" => allocatedActiveResidueSources B U basis S j i hactive q hq r hsize
local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i
local notation "torus" => blockTorusFactor (Fintype.card α) (j.val + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 4

noncomputable def correlatedRetainedFrequencyNNReal (n d : ℕ) (P V ζ : ℝ) : ℝ≥0 :=
  ⟨positiveRetainedFrequencyBound n d P V ζ, positiveRetainedFrequencyBound_nonneg _ _ _ _ _⟩

variable (P : ℝ) (rows : Finset (Finset α)) (ε : ℝ)
local notation "tailOrder" => (layerTailDegree m + 2) * rows.card
local notation "tailWeight" => (2 * (torus : ℝ)) ^ rows.card
local notation "bias" => positiveModerateRetainedBias j.val rows.card tailOrder
  P (4 * (torus : ℝ)) tailWeight ε
local notation "cap" => positiveModerateSpectrumCardBudget j.val rows.card tailOrder
  P (4 * (torus : ℝ)) tailWeight ε
local notation "frequencyBound" => positiveRetainedFrequencyBound j.val rows.card
  P (4 * (torus : ℝ)) bias
local notation "denominatorBound" => positiveRetainedDenominatorBound j.val rows.card tailOrder
  P (4 * (torus : ℝ)) tailWeight bias

theorem exists_allocatedCorrelatedModerate_sites {Cell : Type*}
    (a : Cell → (B ⟨j, Sum.inr i⟩ → ZMod q) → ℂ) (ha : ∀ cell x, ‖a cell x‖ ≤ 1)
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hgamma : gamma ≤ S.value)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (hP : 1 ≤ P)
    (hcLongP : scalarCubePrimitiveEnvelope Empty A 32 (256 * probabilityProfileLipschitz) q ≤ P)
    (hcShortP : scalarCubePrimitiveEnvelope Empty A 1 0
      (scalarCubeNormalizationThreshold Empty q 32 (256 * probabilityProfileLipschitz) + 1) ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hε : 0 < ε) (hε1 : ε ≤ 1) {M : ℕ} [NeZero M] (hM : M = torus * scale)
    (hrows : ∀ s ∈ rows, s.card ≤ j.val + 1) (shift : rows → ℤ)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card tailOrder ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    {Rsite δ Q : ℝ} (hRsite : 0 < Rsite) (hδ : 0 < δ) (hQ : 0 ≤ Q)
    (hRQ : Rsite ≤ Real.exp Q) (hδQ : (δ / (cap + 1))⁻¹ ≤ Real.exp Q)
    (hLQ : ((CircleFourier.characterLipConstant *
      ((rows.card : ℝ≥0) * correlatedRetainedFrequencyNNReal j.val rows.card P (4 * (torus : ℝ)) bias) + 4) *
        (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q) :
    let F := positiveModerateSpectrumCover rows M j.val P (4 * (torus : ℝ)) S.value bias
    ∃ D : F → ℕ, (∀ k, 0 < D k ∧ (D k : ℝ) ≤ denominatorBound) ∧
      ∃ N : F → ℕ, (∀ k, (N k : ℝ) ≤ Real.exp (4 * Q + 8)) ∧
        (Fintype.card (PlateauSiteIndex α F N) : ℝ) ≤
          cap * Real.exp (Fintype.card (Finset α) * (4 * Q + 8)) ∧
        ∃ (c : Cell → PlateauSiteIndex α F N → ℂ)
          (f : (k : PlateauSiteIndex α F N) → Finset α → ZMod (D k.1) → ℝ → ℂ),
          (∀ cell, (∑ k, ‖c cell k‖) ≤ cap *
            Real.exp (Fintype.card (Finset α) * (4 * Q + 8) + Q)) ∧
          (∀ k u z x, ‖f k u z x‖ ≤ 1) ∧
          (∀ k u z, LipschitzWith ⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ (f k u z)) ∧
          ∀ cell (y : Finset α → ℤ), (∀ u, |(y u : ℝ) / scale| ≤ Rsite) →
            ‖(scale : ℂ) ^ rows.card * correlatedModeratePointMass
                (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources
                (fun coeff => a cell (fun b => ((coeff b none : ℤ) : ZMod q)))
                rows (fun _ => 0) shift (fun t => booleanCoefficient y t) -
              ∑ k, c cell k * ∏ u, f k u (y u : ZMod (D k.1)) ((y u : ℝ) / scale)‖ ≤ ε + δ := by
  let F := positiveModerateSpectrumCover rows M j.val P (4 * (torus : ℝ)) S.value bias
  have hK := allocatedPrincipalGridScale_pos B U basis hR S j i hactive
  obtain ⟨hcapF, D, ar, ω, hD, hω, hfreq⟩ := allocatedCorrelatedModerate_retained_modes
    B U basis S j i hactive hR P rows ε hgrid hgamma hP hε hε1 hM
  have hcap : 0 ≤ cap := (Nat.cast_nonneg F.card).trans hcapF
  let (k : F) : NeZero (D k) := ⟨Nat.ne_of_gt (hD k).1⟩
  let β (cell : Cell) (k : F) := correlatedModerateFourierCoefficient
    (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources
    (fun coeff => a cell (fun b => ((coeff b none : ℤ) : ZMod q)))
    (fun _ => 0) M rows 0 k.val
  have hβ (cell : Cell) : (∑ k, ‖β cell k‖) ≤ cap := by
    exact (correlatedModerateFourierCoefficient_retained_mass
      (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources
      (fun coeff => a cell (fun b => ((coeff b none : ℤ) : ZMod q)))
      (fun _ => 0) (fun coeff => ha cell _) rows 0 F).trans hcapF
  have hscale : ((scale : ℝ) / M) ^ rows.card ≤ 1 := by
    rw [hM, Nat.cast_mul]
    exact grid_scale_factor_le_one _ _ _ (blockTorusFactor_pos _ _ _ _) hK
  obtain ⟨N, hN, hNcard, c, f, hc, hf, hLf, herr⟩ := exists_forecastModerate_weighted_sites rows F
    (blockJetScaleBound (Fintype.card α) (j.val + 1) (Fintype.card (B ⟨j, Sum.inr i⟩)) 4)
    hK shift D ar ω
    hfreq β hcap hβ hscale
    (correlatedRetainedFrequencyNNReal j.val rows.card P (4 * (torus : ℝ)) bias)
    hω hRsite hδ hQ hRQ hδQ hLQ
  refine ⟨D, hD, N, hN, ?_, c, f, hc, hf, hLf, ?_⟩
  · exact hNcard.trans (mul_le_mul_of_nonneg_right hcapF (Real.exp_nonneg _))
  · intro cell y hy
    have he := allocatedCorrelatedModeratePlateau_budget_error B U basis S j i hactive q hq r hsize hR
      (a cell) hgrid hgamma (ha cell) A hA P hcLongP hcShortP hsP hε hε1 hM rows hrows
      shift (fun t => booleanCoefficient y t) hB
    have hferr := herr cell y hy
    rw [← correlatedModeratePlateauApproximation_eq_weightedFourierSum
      (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources
      (fun coeff => a cell (fun b => ((coeff b none : ℤ) : ZMod q))) (fun _ => 0)
      (blockJetScaleBound (Fintype.card α) (j.val + 1) (Fintype.card (B ⟨j, Sum.inr i⟩)) 4)
      rows shift (fun t => booleanCoefficient y t) F] at hferr
    exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add he hferr)

end Erdos3.VectorPolynomial

end

end OAI
