import OAI.Combinatorics.Progressions.Fourier.AllocatedCorrelatedModerateSpectrum
import OAI.Combinatorics.Progressions.Probability.CorrelatedModeratePointMass
import OAI.Combinatorics.Progressions.Sampling.AllocatedNaturalGridPoint

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
variable {n K M : ℕ} [NeZero M]
variable (c : B → NormalizedScalarCubeSource Empty)
variable (s : B → Fin n → NormalizedScalarCubeSource I)
variable (a : (∀ b, IntegerScalarCubeBox Empty (c b).length) → ℂ) (offset : B → ℤ)

noncomputable def correlatedModerateFourierCoefficient (M : ℕ) [NeZero M]
    (rows : Finset (Finset I)) (shift : rows → ℤ) (k : rows → Fin M) : ℂ :=
  (weightedModerateIntegerProductSource c s).complexMean (fun x =>
    a (fun b => (x b).1) * rectangularGridCharacter M k
      (weightedModerateIntegerJetSum c s rows offset shift x))

noncomputable def correlatedModerateGridApproximation (K M : ℕ) [NeZero M]
    (rows : Finset (Finset I)) (shift z : rows → ℤ) (F : Finset (rows → Fin M)) : ℂ :=
  ((K : ℂ) / M) ^ rows.card * ∑ k ∈ F,
    correlatedModerateFourierCoefficient c s a offset M rows shift k *
      star (rectangularGridCharacter M k z)

noncomputable def correlatedModeratePlateauApproximation (K : ℕ) (H : ℝ)
    (rows : Finset (Finset I)) (shift z : rows → ℤ) (F : Finset (rows → Fin M)) : ℂ :=
  (normalizedSupportPlateau H (fun t => ((z t : ℝ) - shift t) / K) : ℂ) *
    correlatedModerateGridApproximation c s a offset K M rows shift z F

omit [NeZero M] in
theorem correlatedModeratePointMass_zero_off_scaled_support
    {A : ℝ} (hA : 0 ≤ A)
    (hvol : ∀ b, (|(offset b : ℝ)| + (c b).length) *
      (∏ v, ((s b v).length : ℝ)) ≤ A * K)
    (rows : Finset (Finset I)) (hrows : ∀ t ∈ rows, t.card ≤ n)
    (shift z : rows → ℤ)
    (hz : ¬ ∀ t, |(z t : ℝ) - shift t| ≤
      blockJetScaleBound (Fintype.card I) n (Fintype.card B) A * K) :
    correlatedModeratePointMass c s a rows offset shift z = 0 := by
  have he (x : ∀ b, IntegerScalarCubeBox Empty (c b).length ×
      (∀ j, IntegerScalarCubeBox I (s b j).length)) :
      weightedModerateIntegerJetSum c s rows offset shift x ≠ z := by
    intro hx
    apply hz
    intro t
    have hb := weightedModerateIntegerJetSum_scale_bound c s offset hA
      (Nat.cast_nonneg K) hvol rows hrows shift x t
    simpa only [hx] using hb
  simp only [correlatedModeratePointMass, he, ite_false,
    FiniteProbabilityWeights.complexMean_const]

omit [NeZero M] in
theorem correlatedModeratePointMass_eq_residue_buffered
    {A : ℝ} (hA : 0 ≤ A) (hK : 0 < K)
    (hvol : ∀ b, (|(offset b : ℝ)| + (c b).length) *
      (∏ v, ((s b v).length : ℝ)) ≤ A * K)
    (hM : M = blockTorusFactor (Fintype.card I) n (Fintype.card B) A * K)
    (rows : Finset (Finset I)) (hrows : ∀ t ∈ rows, t.card ≤ n)
    (shift z : rows → ℤ)
    (hz : ∀ t, |(z t : ℝ) - shift t| ≤
      (blockJetScaleBound (Fintype.card I) n (Fintype.card B) A + 1 / 4) * K) :
    correlatedModeratePointMass c s a rows offset shift z =
      (weightedModerateIntegerProductSource c s).complexMean (fun x =>
        if integerGridResidue M (weightedModerateIntegerJetSum c s rows offset shift x) =
          integerGridResidue M z then a (fun b => (x b).1) else 0) := by
  apply FiniteProbabilityWeights.complexMean_congr_support
  intro x _
  have hclose : ∀ t, |weightedModerateIntegerJetSum c s rows offset shift x t - z t| < (M : ℤ) := by
    rw [hM, blockTorusFactor]
    exact scaled_integer_support_close_buffered
      (weightedModerateIntegerJetSum c s rows offset shift x) z shift hK
      (weightedModerateIntegerJetSum_scale_bound c s offset hA (Nat.cast_nonneg K)
        hvol rows hrows shift x) hz
  simp only [integerGridResidue_eq_iff_of_close M
    (weightedModerateIntegerJetSum c s rows offset shift x) z hclose]

theorem correlatedModeratePointMass_error_plateau
    {A : ℝ} (hA : 0 ≤ A) (hK : 0 < K)
    (hvol : ∀ b, (|(offset b : ℝ)| + (c b).length) *
      (∏ v, ((s b v).length : ℝ)) ≤ A * K)
    (hM : M = blockTorusFactor (Fintype.card I) n (Fintype.card B) A * K)
    (rows : Finset (Finset I)) (hrows : ∀ t ∈ rows, t.card ≤ n)
    (shift z : rows → ℤ) (F : Finset (rows → Fin M)) {ε : ℝ} (hε : 0 ≤ ε)
    (htail : spectrumTail F (fun k =>
      ‖correlatedModerateFourierCoefficient c s a offset M rows shift k‖) ≤ ε) :
    ‖(K : ℂ) ^ rows.card * correlatedModeratePointMass c s a rows offset shift z -
      correlatedModeratePlateauApproximation c s a offset K
        (blockJetScaleBound (Fintype.card I) n (Fintype.card B) A) rows shift z F‖ ≤ ε := by
  let H := blockJetScaleBound (Fintype.card I) n (Fintype.card B) A
  let χ := normalizedSupportPlateau H (fun t => ((z t : ℝ) - shift t) / K)
  let v : ℂ := (K : ℂ) ^ rows.card * correlatedModeratePointMass c s a rows offset shift z
  have hχ := normalizedSupportPlateau_range H (fun t => ((z t : ℝ) - shift t) / K)
  have hfix : (χ : ℂ) * v = v := by
    by_cases hz : ∀ t, |(z t : ℝ) - shift t| ≤ H * K
    · have hχ1 : χ = 1 := normalizedSupportPlateau_grid_one
        (blockJetScaleBound_nonneg _ _ _ hA) hK shift z hz
      simp only [hχ1, Complex.ofReal_one, one_mul]
    · have hz0 := correlatedModeratePointMass_zero_off_scaled_support c s a offset hA hvol
        rows hrows shift z hz
      simp only [v, hz0, mul_zero]
  change ‖v - (χ : ℂ) * correlatedModerateGridApproximation c s a offset K M rows shift z F‖ ≤ ε
  by_cases hχ0 : χ = 0
  · have hv : v = 0 := by simpa only [hχ0, Complex.ofReal_zero, zero_mul] using hfix.symm
    simpa only [hv, hχ0, Complex.ofReal_zero, zero_mul, sub_self, norm_zero] using hε
  · have hz := normalizedSupportPlateau_grid_support hK shift z hχ0
    have hd := correlatedModeratePointMass_eq_residue_buffered c s a offset hA hK hvol hM
      rows hrows shift z hz
    have he := weighted_integerGridDensity_error_of_tail
      (weightedModerateIntegerProductSource c s) (weightedModerateIntegerJetSum c s rows offset shift)
      (fun x => a (fun b => (x b).1)) K M F htail z
    simp only [Fintype.card_coe, ← hd] at he
    have hscale : ((K : ℝ) / M) ^ rows.card ≤ 1 := by
      rw [hM, Nat.cast_mul]
      exact grid_scale_factor_le_one _ K rows.card (blockTorusFactor_pos _ _ _ _) hK
    have hv : ‖v - correlatedModerateGridApproximation c s a offset K M rows shift z F‖ ≤ ε :=
      he.trans (mul_le_of_le_one_left hε hscale)
    calc
      _ = ‖(χ : ℂ) * (v - correlatedModerateGridApproximation c s a offset K M rows shift z F)‖ := by
        rw [mul_sub, hfix]
      _ = χ * ‖v - correlatedModerateGridApproximation c s a offset K M rows shift z F‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hχ.1]
      _ ≤ 1 * ε := mul_le_mul hχ.2 hv (norm_nonneg _) zero_le_one
      _ = ε := one_mul ε

end Erdos3

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
variable (a : (B ⟨j, Sum.inr i⟩ → ZMod q) → ℂ)

local notation "sources" => allocatedActiveResidueSources B U basis S j i hactive q hq r hsize
local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i
local notation "torus" => blockTorusFactor (Fintype.card α) (j.val + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 4

noncomputable def allocatedCorrelatedModeratePlateauApproximation (P ζ : ℝ)
    (M : ℕ) [NeZero M] (rows : Finset (Finset α)) (shift z : rows → ℤ) : ℂ :=
  correlatedModeratePlateauApproximation
    (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources
    (fun coeff => a (fun b => ((coeff b none : ℤ) : ZMod q))) (fun _ => 0) scale
    (blockJetScaleBound (Fintype.card α) (j.val + 1) (Fintype.card (B ⟨j, Sum.inr i⟩)) 4)
    rows shift z (positiveModerateSpectrumCover rows M j.val P (4 * (torus : ℝ)) S.value ζ)

theorem allocatedCorrelatedModeratePlateau_error
    (ha : ∀ x, ‖a x‖ ≤ 1)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcLongP : scalarCubePrimitiveEnvelope Empty A 32 (256 * probabilityProfileLipschitz) q ≤ P)
    (hcShortP : scalarCubePrimitiveEnvelope Empty A 1 0
      (scalarCubeNormalizationThreshold Empty q 32 (256 * probabilityProfileLipschitz) + 1) ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {W ζ ε : ℝ} {t M : ℕ} [NeZero M] (hW : 0 ≤ W)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε) (hM : M = torus * scale)
    (rows : Finset (Finset α)) (hrows : ∀ s ∈ rows, s.card ≤ j.val + 1)
    (shift z : rows → ℤ)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card t ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hcard : (M : ℝ) ^ rows.card ≤ W * (S.value : ℝ) ^ t)
    (haccuracy : (2 * positiveModerateSpectrumConstant j.val rows.card P (4 * (torus : ℝ)) *
      2 ^ positiveModerateSpectrumExponent j.val rows.card +
      W * (2 ^ positiveModerateLengthExponent j.val * positiveModerateLengthConstant j.val P) ^ t) * ζ ≤ ε) :
    ‖(scale : ℂ) ^ rows.card * correlatedModeratePointMass
        (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources
        (fun coeff => a (fun b => ((coeff b none : ℤ) : ZMod q))) rows (fun _ => 0) shift z -
      allocatedCorrelatedModeratePlateauApproximation B U basis S j i hactive q hq r hsize hR a
        P ζ M rows shift z‖ ≤ ε := by
  have hgamma : 0 < gamma := principalProfileSize_pos (hR j) _
  have hC : 0 ≤ 2 * (torus : ℝ) * gamma := by positivity
  have hMK : (M : ℝ) ≤ (2 * (torus : ℝ) * gamma) * basisAxisScale (basis j) i := by
    rw [hM, Nat.cast_mul]
    calc
      _ ≤ (torus : ℝ) * (2 * gamma * basisAxisScale (basis j) i) :=
        mul_le_mul_of_nonneg_left
          (allocatedPrincipalGridScale_bounds B U basis hR S j i hactive).2 (Nat.cast_nonneg _)
      _ = _ := by ring
  have hratio : (2 * (torus : ℝ) * gamma) / (2 * gamma) = (torus : ℝ) := by
    field_simp
  have ht := allocatedCorrelatedModerateSpectrum_tail B U basis S j i hactive q hq r hsize hR
    a ha A hA P hcLongP hcShortP hsP hC hW hζ hζ1 hε (Nat.pos_of_ne_zero (NeZero.ne M))
    hMK rows hrows shift hB hcard (by simpa only [hratio] using haccuracy)
  simp only [hratio] at ht
  exact correlatedModeratePointMass_error_plateau
    (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources
    (fun coeff => a (fun b => ((coeff b none : ℤ) : ZMod q))) (fun _ => 0)
    (by norm_num) (allocatedPrincipalGridScale_pos B U basis hR S j i hactive)
    (allocatedActiveResidueSources_natural_volume B U basis hR S q r j i hactive hq hsize)
    hM rows hrows shift z _ hε ht

theorem allocatedCorrelatedModeratePlateau_error_of_grid
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hgamma : gamma ≤ S.value) (ha : ∀ x, ‖a x‖ ≤ 1)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcLongP : scalarCubePrimitiveEnvelope Empty A 32 (256 * probabilityProfileLipschitz) q ≤ P)
    (hcShortP : scalarCubePrimitiveEnvelope Empty A 1 0
      (scalarCubeNormalizationThreshold Empty q 32 (256 * probabilityProfileLipschitz) + 1) ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {ζ ε : ℝ} {M : ℕ} [NeZero M]
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε) (hM : M = torus * scale)
    (rows : Finset (Finset α)) (hrows : ∀ s ∈ rows, s.card ≤ j.val + 1)
    (shift z : rows → ℤ)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 2) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (haccuracy : (2 * positiveModerateSpectrumConstant j.val rows.card P (4 * (torus : ℝ)) *
      2 ^ positiveModerateSpectrumExponent j.val rows.card +
      (2 * (torus : ℝ)) ^ rows.card *
        (2 ^ positiveModerateLengthExponent j.val * positiveModerateLengthConstant j.val P) ^
          ((layerTailDegree m + 2) * rows.card)) * ζ ≤ ε) :
    ‖(scale : ℂ) ^ rows.card * correlatedModeratePointMass
        (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources
        (fun coeff => a (fun b => ((coeff b none : ℤ) : ZMod q))) rows (fun _ => 0) shift z -
      allocatedCorrelatedModeratePlateauApproximation B U basis S j i hactive q hq r hsize hR a
        P ζ M rows shift z‖ ≤ ε := by
  have hMN : (M : ℝ) ≤ (torus : ℝ) * scale := by
    simp only [hM, Nat.cast_mul, le_refl]
  have hcard := allocatedPrincipalGridScale_cardinality B U basis hR S j i hactive
    hgrid hgamma (Nat.cast_nonneg torus) hMN rows.card
  exact allocatedCorrelatedModeratePlateau_error B U basis S j i hactive q hq r hsize hR a
    ha A hA P hcLongP hcShortP hsP (by positivity) hζ hζ1 hε hM rows hrows shift z hB hcard haccuracy

noncomputable def allocatedCorrelatedModeratePlateauBudgetApproximation (P ε : ℝ)
    (M : ℕ) [NeZero M] (rows : Finset (Finset α)) (shift z : rows → ℤ) : ℂ :=
  allocatedCorrelatedModeratePlateauApproximation B U basis S j i hactive q hq r hsize hR a P
    (positiveModerateRetainedBias j.val rows.card ((layerTailDegree m + 2) * rows.card)
      P (4 * (torus : ℝ)) ((2 * (torus : ℝ)) ^ rows.card) ε) M rows shift z

theorem allocatedCorrelatedModeratePlateau_budget_error
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hgamma : gamma ≤ S.value) (ha : ∀ x, ‖a x‖ ≤ 1)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcLongP : scalarCubePrimitiveEnvelope Empty A 32 (256 * probabilityProfileLipschitz) q ≤ P)
    (hcShortP : scalarCubePrimitiveEnvelope Empty A 1 0
      (scalarCubeNormalizationThreshold Empty q 32 (256 * probabilityProfileLipschitz) + 1) ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {ε : ℝ} {M : ℕ} [NeZero M] (hε : 0 < ε) (hε1 : ε ≤ 1) (hM : M = torus * scale)
    (rows : Finset (Finset α)) (hrows : ∀ s ∈ rows, s.card ≤ j.val + 1)
    (shift z : rows → ℤ)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 2) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) :
    ‖(scale : ℂ) ^ rows.card * correlatedModeratePointMass
        (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources
        (fun coeff => a (fun b => ((coeff b none : ℤ) : ZMod q))) rows (fun _ => 0) shift z -
      allocatedCorrelatedModeratePlateauBudgetApproximation B U basis S j i hactive q hq r hsize hR a
        P ε M rows shift z‖ ≤ ε := by
  have hP : 1 ≤ P :=
    (fixedPositiveCoefficientSource_primitive
      (scalarCubeNormalizationThreshold Empty q 32 (256 * probabilityProfileLipschitz)) A).one_le.trans hcShortP
  obtain ⟨hζ, hζ1, hacc⟩ := positiveModerateRetainedBias_spec j.val rows.card
    ((layerTailDegree m + 2) * rows.card) (V := 4 * (torus : ℝ)) hP
    (by positivity : (0 : ℝ) ≤ (2 * (torus : ℝ)) ^ rows.card) hε hε1
  exact allocatedCorrelatedModeratePlateau_error_of_grid B U basis S j i hactive q hq r hsize hR a
    hgrid hgamma ha A hA P hcLongP hcShortP hsP hζ hζ1 hε.le hM rows hrows shift z hB hacc

omit [∀ a, DecidableEq (B a)] in
include hR hactive in
theorem allocatedCorrelatedModeratePlateau_cover_card
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hgamma : gamma ≤ S.value) {P ε : ℝ} {M : ℕ}
    (hP : 1 ≤ P) (hε : 0 < ε) (hε1 : ε ≤ 1) (hM : M = torus * scale)
    (rows : Finset (Finset α)) :
    ((positiveModerateSpectrumCover rows M j.val P (4 * (torus : ℝ)) S.value
      (positiveModerateRetainedBias j.val rows.card ((layerTailDegree m + 2) * rows.card)
        P (4 * (torus : ℝ)) ((2 * (torus : ℝ)) ^ rows.card) ε)).card : ℝ) ≤
      positiveModerateSpectrumCardBudget j.val rows.card ((layerTailDegree m + 2) * rows.card)
        P (4 * (torus : ℝ)) ((2 * (torus : ℝ)) ^ rows.card) ε := by
  have hMN : (M : ℝ) ≤ (torus : ℝ) * scale := by
    simp only [hM, Nat.cast_mul, le_refl]
  have hcard := allocatedPrincipalGridScale_cardinality B U basis hR S j i hactive
    hgrid hgamma (Nat.cast_nonneg torus) hMN rows.card
  have hc := positiveModerateSpectrumCover_card_budget rows M j.val
    ((layerTailDegree m + 2) * rows.card) hP
    (by positivity : (0 : ℝ) ≤ 4 * (torus : ℝ))
    (by positivity : (0 : ℝ) ≤ (2 * (torus : ℝ)) ^ rows.card)
    (Nat.cast_nonneg S.value) hε hε1 (by simpa only [Fintype.card_coe] using hcard)
  simpa only [Fintype.card_coe] using hc

end Erdos3.VectorPolynomial

end

end OAI
