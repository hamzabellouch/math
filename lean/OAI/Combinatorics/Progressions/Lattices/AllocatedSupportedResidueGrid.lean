import OAI.Combinatorics.Progressions.Fourier.AllocatedSupportedResidueSpectrum

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

noncomputable def allocatedSupportedGridDensity (M : ℕ) (rows : Finset (Finset α))
    (shift z : rows → ℤ) : ℝ :=
  (basisAxisScale (basis j) i : ℝ) ^ rows.card *
    (((allocatedSupportedResidueJetPMF B U basis hR hσ S q r hcell j i rows shift).map
      (integerGridResidue M)) (integerGridResidue M z)).toReal

variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)

local notation "sources" => allocatedActiveResidueSources B U basis S j i hactive q hq r hsize
local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

theorem allocatedSupportedGridDensity_eq_normalized (M : ℕ) (rows : Finset (Finset α))
    (shift z : rows → ℤ) :
    allocatedSupportedGridDensity B U basis hR hσ S q r hcell j i M rows shift z =
      integerGridDensity (weightedModerateIntegerProductSource
        (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources)
        (weightedModerateIntegerJetSum (fun _ => csource) sources rows (fun _ => 0) shift)
        (basisAxisScale (basis j) i) M z := by
  have h := integerGridDensity_eq_of_pmf_image
    (weightedModerateIntegerProductSource (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources)
    (weightedModerateIntegerJetSum (fun _ => csource) sources rows (fun _ => 0) shift) _
    (allocatedSupportedResidueJetPMF_source B U basis hR hσ S q r hcell j i
      hactive hq hsize rows shift) (basisAxisScale (basis j) i) M z
  simpa only [allocatedSupportedGridDensity, Fintype.card_coe] using h.symm

noncomputable def allocatedSupportedGridApproximation (P C ε : ℝ) (M : ℕ) [NeZero M]
    (rows : Finset (Finset α)) (shift z : rows → ℤ) : ℂ :=
  weightedModerateGridApproximation (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources
    (basisAxisScale (basis j) i) M rows (fun _ => 0) shift z
    (positiveModerateSpectrumCover rows M j.val P (C / (2 * gamma)) S.value
      (positiveModerateRetainedBias j.val rows.card ((layerTailDegree m + 1) * rows.card)
        P (C / (2 * gamma)) (C ^ rows.card) ε))

theorem allocatedSupportedGridDensity_error_of_tail
    (M : ℕ) [NeZero M] (rows : Finset (Finset α)) (shift z : rows → ℤ)
    (F : Finset (rows → Fin M)) {ε : ℝ}
    (htail : spectrumTail F (fun k => ‖∏ b : B ⟨j, Sum.inr i⟩,
      weightedModerateGridCoefficient csource ((sources) b) 0 M rows k‖) ≤ ε) :
    ‖(allocatedSupportedGridDensity B U basis hR hσ S q r hcell j i M rows shift z : ℂ) -
      weightedModerateGridApproximation (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources
        (basisAxisScale (basis j) i) M rows (fun _ => 0) shift z F‖ ≤
      ((basisAxisScale (basis j) i : ℝ) / M) ^ rows.card * ε := by
  have he := congrArg (fun x : ℝ => ‖(x : ℂ) -
    weightedModerateGridApproximation (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources
      (basisAxisScale (basis j) i) M rows (fun _ => 0) shift z F‖)
    (allocatedSupportedGridDensity_eq_normalized B U basis hR hσ S q r hcell j i hactive hq hsize
      M rows shift z)
  exact he.trans_le (weightedModerateGridDensity_error_of_tail
    (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources (basisAxisScale (basis j) i) M rows (fun _ => 0)
    F (by simpa only [Int.cast_zero] using htail) shift z)

theorem allocatedSupportedGridDensity_error
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {C ε : ℝ} {M : ℕ} [NeZero M] (hC : 0 ≤ C)
    (hMK : (M : ℝ) ≤ C * basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) (shift z : rows → ℤ) :
    ‖(allocatedSupportedGridDensity B U basis hR hσ S q r hcell j i M rows shift z : ℂ) -
      allocatedSupportedGridApproximation B U basis hR S q r j i hactive hq hsize P C ε M rows shift z‖ ≤
        ((basisAxisScale (basis j) i : ℝ) / M) ^ rows.card * ε := by
  exact allocatedSupportedGridDensity_error_of_tail B U basis hR hσ S q r hcell j i hactive hq hsize
    M rows shift z _ (allocatedSupportedResidueSpectrum_tail B U basis hR S j i hactive q hq r hsize
      hgrid A hA P hcP hsP hC (Nat.pos_of_ne_zero (NeZero.ne M)) hMK rows hrows hB hε hε1)

end Erdos3.VectorPolynomial

end

end OAI
