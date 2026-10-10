import OAI.Combinatorics.Progressions.Estimates.AllocatedPrincipalSourceScale
import OAI.Combinatorics.Progressions.Lattices.ContainedFullIntervalResidueIdentity

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : ∀ v, (Fintype.card α + 1) * q ≤ allocatedPrincipalSides B U basis S v)
variable (j : Fin m) (i : Fin (n j))

noncomputable def allocatedPrincipalResidueSources (b : B ⟨j, Sum.inr i⟩) :
    Fin (j.val + 1) → NormalizedScalarCubeSource α :=
  fun v => principalResidueNormalizedSource B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
    q hq r hsize ⟨⟨j, Sum.inr i⟩, b, v⟩

local notation "sources" => allocatedPrincipalResidueSources B U basis S q hq r hsize j i

variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)

include hactive in
theorem allocatedPrincipalResidueSources_length (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)) :
    ((sources) b v).length = S.value :=
  allocatedPrincipalSides_active B U basis S j i hactive b v

omit hactive in
theorem allocatedPrincipalResidueSources_primitive
    (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)) (A : ℝ≥0) :
    ScalarCubePrimitiveBudget ((sources) b v) A (scalarCubePrimitiveEnvelope α A 1 0 q) :=
  principalResidueNormalizedSource_primitive B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
    q hq r hsize ⟨⟨j, Sum.inr i⟩, b, v⟩ A

variable (hR : ∀ j, 0 < R j)

local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

theorem allocatedPrincipalResidueSpectrum_tail
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {C W ζ ε : ℝ} {t M : ℕ} (hC : 0 ≤ C) (hW : 0 ≤ W)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε) (hM : 0 < M)
    (hMK : (M : ℝ) ≤ C * basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (hrows : ∀ s ∈ rows, s.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card t ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hcard : (M : ℝ) ^ rows.card ≤ W * (S.value : ℝ) ^ t)
    (haccuracy : (2 * positiveModerateSpectrumConstant j.val rows.card P (C / (2 * gamma)) *
        2 ^ positiveModerateSpectrumExponent j.val rows.card +
      W * (2 ^ positiveModerateLengthExponent j.val * positiveModerateLengthConstant j.val P) ^ t) * ζ ≤ ε) :
    spectrumTail
      (positiveModerateSpectrumCover rows M j.val P (C / (2 * gamma)) S.value ζ)
      (fun k => ‖∏ b : B ⟨j, Sum.inr i⟩,
        weightedModerateGridCoefficient csource ((sources) b) 0 M rows k‖) ≤ ε := by
  have hc : ScalarCubePrimitiveBudget csource A P :=
    (allocatedPrincipalNormalizedSource_primitive B U basis hR S j i hactive A).mono hcP
  have hs (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)) :
      ScalarCubePrimitiveBudget ((sources) b v) A P :=
    (allocatedPrincipalResidueSources_primitive B U basis S q hq r hsize j i b v A).mono hsP
  have hlength (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)) :
      (S.value : ℝ) ≤ ((sources) b v).length := by
    rw [allocatedPrincipalResidueSources_length B U basis S q hq r hsize j i hactive b v]
  have hproduct (b : B ⟨j, Sum.inr i⟩) :
      (∏ v : Fin (j.val + 1), (((sources) b v).length : ℝ)) =
        (S.value : ℝ) ^ (j.val + 1) := by
    simp only [allocatedPrincipalResidueSources_length B U basis S q hq r hsize j i hactive,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hscale (b : B ⟨j, Sum.inr i⟩) :
      (M : ℝ) / (((csource).length : ℝ) * ∏ v, (((sources) b v).length : ℝ)) ≤
        C / (2 * gamma) := by
    rw [hproduct b]
    exact allocatedPrincipalNormalizedSource_grid_ratio B U basis hR S j i hactive hC hMK
  have hgamma : 0 < gamma := principalProfileSize_pos (hR j) _
  exact weightedPositiveModerate_uniform_spectrum_tail
    (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources A hA hc.one_le (fun _ => hc) hs
    (fun _ z hz => allocatedPrincipalNormalizedSource_positive_support B U basis hR S j i hactive z hz)
    (div_nonneg hC (by positivity)) hW (Nat.cast_nonneg S.value) hζ hζ1 hε hlength hM hscale
    rows hrows hB hcard haccuracy

end Erdos3.VectorPolynomial

end

end OAI
