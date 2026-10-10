import OAI.Combinatorics.Progressions.Estimates.AllocatedPrincipalSourceScale
import OAI.Combinatorics.Progressions.Lattices.AllocatedResidueInterpolationMixture
import OAI.Combinatorics.Progressions.Lattices.WeightedIntegerGridDensityTail

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {K T γ : ℝ} (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
  (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))
  (q : ℕ) [NeZero q] (hq : 0 < q)

include hq in
theorem principalCorrelatedModerate_spectrum_tail
    {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I] {n : ℕ}
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (a : (B → ZMod q) → ℂ) (ha : ∀ r, ‖a r‖ ≤ 1)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ζ ε : ℝ} {t : ℕ}
    (hUlong : scalarCubePrimitiveEnvelope Empty A 32 (256 * probabilityProfileLipschitz) q ≤ U)
    (hUshort : scalarCubePrimitiveEnvelope Empty A 1 0
      (scalarCubeNormalizationThreshold Empty q 32 (256 * probabilityProfileLipschitz) + 1) ≤ U)
    (hs : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε)
    (hlen : ∀ b j, L ≤ (s b j).length)
    {M : ℕ} [NeZero M] (hM : 0 < M)
    (hscale : ∀ b, (M : ℝ) / ((principalIntervalLength K T γ : ℝ) *
      ∏ j, ((s b j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1) (shift : J → ℤ)
    (hB : positiveModerateSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t)
    (haccuracy : (2 * positiveModerateSpectrumConstant n J.card U (4 * V) *
      2 ^ positiveModerateSpectrumExponent n J.card +
      W * (2 ^ positiveModerateLengthExponent n * positiveModerateLengthConstant n U) ^ t) * ζ ≤ ε) :
    spectrumTail (positiveModerateSpectrumCover J M n U (4 * V) L ζ)
      (fun k => ‖(weightedModerateIntegerProductSource
        (fun _ : B => principalNormalizedSource hK hT hγ hlarge) s).complexMean (fun x =>
          a (fun b => ((x b).1 none : ℤ)) * rectangularGridCharacter M k
            (weightedModerateIntegerJetSum
              (fun _ : B => principalNormalizedSource hK hT hγ hlarge) s J
              (fun _ => 0) shift x))‖) ≤ ε := by
  let N := scalarCubeNormalizationThreshold Empty q 32 (256 * probabilityProfileLipschitz)
  by_cases hlong : N ≤ principalIntervalLength K T γ
  · simp_rw [weightedModerateIntegerJetSum_residue_coefficient,
      norm_mul, rectangularGridCharacter_norm, one_mul]
    apply principalCoefficientResidue_correlated_spectrum_tail hK hT hγ hlarge q hq hlong
      s a ha A hA hUlong hs (by positivity) hW hL hζ hζ1 hε hlen hM
      (fun b => (hscale b).trans (by linarith)) J hJ hB hsize haccuracy
  · exact weightedModerateIntegerProductSource_short_correlated_spectrum_tail
      (fun _ : B => principalNormalizedSource hK hT hγ hlarge) s
      (fun z => a (fun b => ((z b none : ℤ) : ZMod q))) (fun z => ha _)
      (fun _ => principalNormalizedSource_positive_support hK hT hγ hlarge)
      (fun _ => (Nat.lt_of_not_ge hlong).le) A hA
      ((fixedPositiveCoefficientSource_primitive N A).one_le.trans hUshort)
      hUshort hs hV hW hL hζ hζ1 hε hlen hM hscale J hJ shift hB hsize haccuracy

include hq in

theorem principalCorrelatedModerate_gridDensity_error
    {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I] {n : ℕ}
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (a : (B → ZMod q) → ℂ) (ha : ∀ r, ‖a r‖ ≤ 1)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ζ ε : ℝ} {t : ℕ}
    (hUlong : scalarCubePrimitiveEnvelope Empty A 32 (256 * probabilityProfileLipschitz) q ≤ U)
    (hUshort : scalarCubePrimitiveEnvelope Empty A 1 0
      (scalarCubeNormalizationThreshold Empty q 32 (256 * probabilityProfileLipschitz) + 1) ≤ U)
    (hs : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε)
    (hlen : ∀ b j, L ≤ (s b j).length)
    {M : ℕ} [NeZero M] (hM : 0 < M)
    (hscale : ∀ b, (M : ℝ) / ((principalIntervalLength K T γ : ℝ) *
      ∏ j, ((s b j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1) (shift : J → ℤ)
    (hB : positiveModerateSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t)
    (haccuracy : (2 * positiveModerateSpectrumConstant n J.card U (4 * V) *
      2 ^ positiveModerateSpectrumExponent n J.card +
      W * (2 ^ positiveModerateLengthExponent n * positiveModerateLengthConstant n U) ^ t) * ζ ≤ ε)
    (Kgrid : ℕ) (z : J → ℤ) :
    ‖(Kgrid : ℂ) ^ J.card *
        (weightedModerateIntegerProductSource
          (fun _ : B => principalNormalizedSource hK hT hγ hlarge) s).complexMean
          (fun x => if integerGridResidue M (weightedModerateIntegerJetSum
              (fun _ : B => principalNormalizedSource hK hT hγ hlarge) s J
              (fun _ => 0) shift x) = integerGridResidue M z
            then a (fun b => ((x b).1 none : ℤ)) else 0) -
      ((Kgrid : ℂ) / M) ^ J.card *
        ∑ k ∈ positiveModerateSpectrumCover J M n U (4 * V) L ζ,
          (weightedModerateIntegerProductSource
            (fun _ : B => principalNormalizedSource hK hT hγ hlarge) s).complexMean
            (fun x => a (fun b => ((x b).1 none : ℤ)) * rectangularGridCharacter M k
              (weightedModerateIntegerJetSum
                (fun _ : B => principalNormalizedSource hK hT hγ hlarge) s J
                (fun _ => 0) shift x)) * star (rectangularGridCharacter M k z)‖ ≤
      ((Kgrid : ℝ) / M) ^ J.card * ε := by
  have ht := principalCorrelatedModerate_spectrum_tail hK hT hγ hlarge q hq
    s a ha A hA hUlong hUshort hs hV hW hL hζ hζ1 hε hlen hM hscale J hJ shift
    hB hsize haccuracy
  simpa only [Fintype.card_coe] using weighted_integerGridDensity_error_of_tail
    (weightedModerateIntegerProductSource
      (fun _ : B => principalNormalizedSource hK hT hγ hlarge) s)
    (weightedModerateIntegerJetSum
      (fun _ : B => principalNormalizedSource hK hT hγ hlarge) s J (fun _ => 0) shift)
    (fun x => a (fun b => ((x b).1 none : ℤ))) Kgrid M
    (positiveModerateSpectrumCover J M n U (4 * V) L ζ) ht z

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

local notation "sources" => allocatedActiveResidueSources B U basis S j i hactive q hq r hsize
local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

theorem allocatedCorrelatedModerateSpectrum_tail
    (a : (B ⟨j, Sum.inr i⟩ → ZMod q) → ℂ) (ha : ∀ x, ‖a x‖ ≤ 1)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcLongP : scalarCubePrimitiveEnvelope Empty A 32 (256 * probabilityProfileLipschitz) q ≤ P)
    (hcShortP : scalarCubePrimitiveEnvelope Empty A 1 0
      (scalarCubeNormalizationThreshold Empty q 32 (256 * probabilityProfileLipschitz) + 1) ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {C W ζ ε : ℝ} {t M : ℕ} [NeZero M] (hC : 0 ≤ C) (hW : 0 ≤ W)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε) (hM : 0 < M)
    (hMK : (M : ℝ) ≤ C * basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (hrows : ∀ s ∈ rows, s.card ≤ j.val + 1)
    (shift : rows → ℤ)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card t ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hcard : (M : ℝ) ^ rows.card ≤ W * (S.value : ℝ) ^ t)
    (haccuracy : (2 * positiveModerateSpectrumConstant j.val rows.card P (4 * (C / (2 * gamma))) *
      2 ^ positiveModerateSpectrumExponent j.val rows.card +
      W * (2 ^ positiveModerateLengthExponent j.val * positiveModerateLengthConstant j.val P) ^ t) * ζ ≤ ε) :
    spectrumTail
      (positiveModerateSpectrumCover rows M j.val P (4 * (C / (2 * gamma))) S.value ζ)
      (fun k => ‖(weightedModerateIntegerProductSource
        (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources).complexMean (fun x =>
          a (fun b => ((x b).1 none : ℤ)) * rectangularGridCharacter M k
            (weightedModerateIntegerJetSum
              (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources rows (fun _ => 0) shift x))‖) ≤ ε := by
  have hs (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)) :
      ScalarCubePrimitiveBudget ((sources) b v) A P :=
    (allocatedActiveResidueSources_primitive B U basis S j i hactive q hq r hsize b v A).mono hsP
  have hlength (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)) :
      (S.value : ℝ) ≤ ((sources) b v).length := by
    rw [allocatedActiveResidueSources_length B U basis S j i hactive q hq r hsize b v]
  have hproduct (b : B ⟨j, Sum.inr i⟩) :
      (∏ v : Fin (j.val + 1), (((sources) b v).length : ℝ)) =
        (S.value : ℝ) ^ (j.val + 1) := by
    simp only [allocatedActiveResidueSources_length B U basis S j i hactive q hq r hsize,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hscale (b : B ⟨j, Sum.inr i⟩) :
      (M : ℝ) / (((csource).length : ℝ) * ∏ v, (((sources) b v).length : ℝ)) ≤
        C / (2 * gamma) := by
    rw [hproduct b]
    exact allocatedPrincipalNormalizedSource_grid_ratio B U basis hR S j i hactive hC hMK
  have hgamma : 0 < gamma := principalProfileSize_pos (hR j) _
  exact principalCorrelatedModerate_spectrum_tail
    (K := (basisAxisScale (basis j) i : ℝ)) (T := (S.value : ℝ) ^ (j.val + 1)) (γ := gamma)
    (by exact_mod_cast basisAxisScale_pos (basis j) i)
    (pow_pos (by exact_mod_cast S.positive) _) hgamma
    (integerAxisPrincipal_width (Nat.zero_lt_succ _) S.positive hgamma (S.gap j i hactive))
    q hq sources a ha A hA hcLongP hcShortP hs (div_nonneg hC (by positivity)) hW
    (Nat.cast_nonneg S.value) hζ hζ1 hε hlength hM hscale rows hrows shift hB hcard haccuracy

theorem allocatedCorrelatedModerate_gridDensity_error
    (a : (B ⟨j, Sum.inr i⟩ → ZMod q) → ℂ) (ha : ∀ x, ‖a x‖ ≤ 1)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcLongP : scalarCubePrimitiveEnvelope Empty A 32 (256 * probabilityProfileLipschitz) q ≤ P)
    (hcShortP : scalarCubePrimitiveEnvelope Empty A 1 0
      (scalarCubeNormalizationThreshold Empty q 32 (256 * probabilityProfileLipschitz) + 1) ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {C W ζ ε : ℝ} {t M : ℕ} [NeZero M] (hC : 0 ≤ C) (hW : 0 ≤ W)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε) (hM : 0 < M)
    (hMK : (M : ℝ) ≤ C * basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (hrows : ∀ s ∈ rows, s.card ≤ j.val + 1)
    (shift : rows → ℤ)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card t ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hcard : (M : ℝ) ^ rows.card ≤ W * (S.value : ℝ) ^ t)
    (haccuracy : (2 * positiveModerateSpectrumConstant j.val rows.card P (4 * (C / (2 * gamma))) *
      2 ^ positiveModerateSpectrumExponent j.val rows.card +
      W * (2 ^ positiveModerateLengthExponent j.val * positiveModerateLengthConstant j.val P) ^ t) * ζ ≤ ε)
    (Kgrid : ℕ) (z : rows → ℤ) :
    ‖(Kgrid : ℂ) ^ rows.card *
        (weightedModerateIntegerProductSource
          (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources).complexMean
          (fun x => if integerGridResidue M (weightedModerateIntegerJetSum
              (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources rows (fun _ => 0) shift x) =
                integerGridResidue M z
            then a (fun b => ((x b).1 none : ℤ)) else 0) -
      ((Kgrid : ℂ) / M) ^ rows.card *
        ∑ k ∈ positiveModerateSpectrumCover rows M j.val P (4 * (C / (2 * gamma))) S.value ζ,
          (weightedModerateIntegerProductSource
            (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources).complexMean
            (fun x => a (fun b => ((x b).1 none : ℤ)) * rectangularGridCharacter M k
              (weightedModerateIntegerJetSum
                (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources rows (fun _ => 0) shift x)) *
            star (rectangularGridCharacter M k z)‖ ≤
      ((Kgrid : ℝ) / M) ^ rows.card * ε := by
  have ht := allocatedCorrelatedModerateSpectrum_tail B U basis S j i hactive q hq r hsize hR
    a ha A hA P hcLongP hcShortP hsP hC hW hζ hζ1 hε hM hMK rows hrows shift hB hcard haccuracy
  simpa only [Fintype.card_coe] using weighted_integerGridDensity_error_of_tail
    (weightedModerateIntegerProductSource (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources)
    (weightedModerateIntegerJetSum
      (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources rows (fun _ => 0) shift)
    (fun x => a (fun b => ((x b).1 none : ℤ))) Kgrid M
    (positiveModerateSpectrumCover rows M j.val P (4 * (C / (2 * gamma))) S.value ζ) ht z

end Erdos3.VectorPolynomial

end

end OAI
