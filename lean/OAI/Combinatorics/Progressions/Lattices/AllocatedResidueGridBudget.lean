import OAI.Combinatorics.Progressions.Fourier.AllocatedGridSpectrumSize
import OAI.Combinatorics.Progressions.Fourier.AllocatedResidueSpectrum

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
variable (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : ∀ v, (Fintype.card α + 1) * q ≤ allocatedPrincipalSides B U basis S v)
variable (j : Fin m) (i : Fin (n j))

local notation "sides" => allocatedPrincipalSides B U basis S
local notation "sidepos" => allocatedPrincipalSides_pos B U basis S
local notation "sources" => allocatedPrincipalResidueSources B U basis S q hq r hsize j i

noncomputable def allocatedPrincipalResidueJetPMF (rows : Finset (Finset α)) (shift : rows → ℤ) :
    PMF (rows → ℤ) :=
  (dependentProductPMF (fun b : B ⟨j, Sum.inr i⟩ =>
    allocatedLayerIntegerPMFs B U basis hR hσ S j i
      (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b))).bind
    (fun z => (principalResidueWeights B (layerSamplerDegree I n) sides sidepos q hq r hsize).toPMF.map
      (fun y => shift + ∑ b : B ⟨j, Sum.inr i⟩, fun row : rows =>
        z b * integerBooleanBlockJet
          (fun v : Fin (j.val + 1) => fun k => (y ⟨⟨j, Sum.inr i⟩, b, v⟩ k : ℤ)) row))

variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

theorem allocatedPrincipalResidueJetPMF_eq_normalized
    (rows : Finset (Finset α)) (shift : rows → ℤ) :
    allocatedPrincipalResidueJetPMF B U basis hR hσ S q hq r hsize j i rows shift =
      principalResidueAxisJetPMF B (layerSamplerDegree I n) sides sidepos q hq r hsize
        ⟨j, Sum.inr i⟩ (fun _ => csource) rows (fun _ => 0) shift := by
  have hc :
      (dependentProductPMF (fun _ : B ⟨j, Sum.inr i⟩ =>
        (csource).source.toPMF.map (fun x => (x none : ℤ)))) =
      dependentProductPMF (fun b : B ⟨j, Sum.inr i⟩ =>
        allocatedLayerIntegerPMFs B U basis hR hσ S j i
          (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b)) :=
    congrArg (fun p : B ⟨j, Sum.inr i⟩ → PMF ℤ => dependentProductPMF p)
      (funext (fun b => allocatedPrincipalNormalizedSource_law B U basis hR hσ S j i hactive b))
  have he := congrArg (fun p : PMF (B ⟨j, Sum.inr i⟩ → ℤ) => p.bind (fun z =>
    (principalResidueWeights B (layerSamplerDegree I n) sides sidepos q hq r hsize).toPMF.map
      (fun y => shift + ∑ b : B ⟨j, Sum.inr i⟩, fun row : rows =>
        z b * integerBooleanBlockJet
          (fun v : Fin (j.val + 1) => fun k => (y ⟨⟨j, Sum.inr i⟩, b, v⟩ k : ℤ)) row))) hc.symm
  unfold allocatedPrincipalResidueJetPMF principalResidueAxisJetPMF
  simp only [zero_add]
  exact he

theorem allocatedPrincipalResidueGridDensity_eq_normalized
    (rows : Finset (Finset α)) (shift : rows → ℤ) (M : ℕ) (z : rows → ℤ) :
    (basisAxisScale (basis j) i : ℝ) ^ rows.card *
      (((allocatedPrincipalResidueJetPMF B U basis hR hσ S q hq r hsize j i rows shift).map
        (integerGridResidue M)) (integerGridResidue M z)).toReal =
      principalResidueAxisGridDensity B (layerSamplerDegree I n) sides sidepos q hq r hsize
        ⟨j, Sum.inr i⟩ (fun _ => csource) rows (fun _ => 0) shift (basisAxisScale (basis j) i) M z := by
  have he := congrArg (fun μ : PMF (rows → ℤ) =>
    (basisAxisScale (basis j) i : ℝ) ^ rows.card *
      ((μ.map (integerGridResidue M)) (integerGridResidue M z)).toReal)
    (allocatedPrincipalResidueJetPMF_eq_normalized B U basis hR hσ S q hq r hsize j i hactive rows shift)
  simpa only [principalResidueAxisGridDensity] using he

theorem allocatedPrincipalResidueGridDensity_error_of_tail
    (rows : Finset (Finset α)) (shift : rows → ℤ) (M : ℕ) [NeZero M]
    (F : Finset (rows → Fin M)) {ε : ℝ}
    (htail : spectrumTail F (fun k => ‖∏ b : B ⟨j, Sum.inr i⟩,
      weightedModerateGridCoefficient csource ((sources) b) 0 M rows k‖) ≤ ε)
    (z : rows → ℤ) :
    ‖(((basisAxisScale (basis j) i : ℝ) ^ rows.card *
        (((allocatedPrincipalResidueJetPMF B U basis hR hσ S q hq r hsize j i rows shift).map
          (integerGridResidue M)) (integerGridResidue M z)).toReal : ℝ) : ℂ) -
      weightedModerateGridApproximation (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources
        (basisAxisScale (basis j) i) M rows (fun _ => 0) shift z F‖ ≤
      ((basisAxisScale (basis j) i : ℝ) / M) ^ rows.card * ε := by
  have hsources : sources = (fun (b : B ⟨j, Sum.inr i⟩)
      (v : Fin (layerSamplerDegree I n ⟨j, Sum.inr i⟩)) =>
        principalResidueNormalizedSource B (layerSamplerDegree I n) sides sidepos q hq r hsize
          ⟨⟨j, Sum.inr i⟩, b, v⟩) := rfl
  simp only [hsources] at htail ⊢
  have he := principalResidueAxisGridDensity_error_of_tail B (layerSamplerDegree I n)
    sides sidepos q hq r hsize ⟨j, Sum.inr i⟩ (fun _ => csource) rows (fun _ => 0) shift
    (basisAxisScale (basis j) i) M F (by
      simp only [Int.cast_zero]
      exact htail) z
  have hd := allocatedPrincipalResidueGridDensity_eq_normalized B U basis hR hσ S q hq r hsize
    j i hactive rows shift M z
  exact (congrArg (fun x : ℝ => ‖(x : ℂ) -
    weightedModerateGridApproximation (fun _ : B ⟨j, Sum.inr i⟩ => csource)
      (fun (b : B ⟨j, Sum.inr i⟩) (v : Fin (layerSamplerDegree I n ⟨j, Sum.inr i⟩)) =>
        principalResidueNormalizedSource B (layerSamplerDegree I n) sides sidepos q hq r hsize
          ⟨⟨j, Sum.inr i⟩, b, v⟩)
      (basisAxisScale (basis j) i) M rows (fun _ => 0) shift z F‖) hd).trans_le he

theorem allocatedPrincipalResidueGridDensity_error
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {C W ζ ε : ℝ} {t M : ℕ} [NeZero M] (hC : 0 ≤ C) (hW : 0 ≤ W)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε)
    (hMK : (M : ℝ) ≤ C * basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (hrows : ∀ s ∈ rows, s.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card t ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hcard : (M : ℝ) ^ rows.card ≤ W * (S.value : ℝ) ^ t)
    (haccuracy : (2 * positiveModerateSpectrumConstant j.val rows.card P (C / (2 * gamma)) *
        2 ^ positiveModerateSpectrumExponent j.val rows.card +
      W * (2 ^ positiveModerateLengthExponent j.val * positiveModerateLengthConstant j.val P) ^ t) * ζ ≤ ε)
    (shift z : rows → ℤ) :
    ‖(((basisAxisScale (basis j) i : ℝ) ^ rows.card *
        (((allocatedPrincipalResidueJetPMF B U basis hR hσ S q hq r hsize j i rows shift).map
          (integerGridResidue M)) (integerGridResidue M z)).toReal : ℝ) : ℂ) -
      weightedModerateGridApproximation (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources
        (basisAxisScale (basis j) i) M rows (fun _ => 0) shift z
          (positiveModerateSpectrumCover rows M j.val P (C / (2 * gamma)) S.value ζ)‖ ≤
      ((basisAxisScale (basis j) i : ℝ) / M) ^ rows.card * ε := by
  exact allocatedPrincipalResidueGridDensity_error_of_tail B U basis hR hσ S q hq r hsize
    j i hactive rows shift M
    (positiveModerateSpectrumCover rows M j.val P (C / (2 * gamma)) S.value ζ)
    (allocatedPrincipalResidueSpectrum_tail B U basis S q hq r hsize j i hactive hR
      A hA P hcP hsP hC hW hζ hζ1 hε (Nat.pos_of_ne_zero (NeZero.ne M)) hMK
      rows hrows hB hcard haccuracy) z

end Erdos3.VectorPolynomial

end

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
variable (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : ∀ v, (Fintype.card α + 1) * q ≤ allocatedPrincipalSides B U basis S v)
variable (j : Fin m) (i : Fin (n j))

local notation "sides" => allocatedPrincipalSides B U basis S
local notation "sidepos" => allocatedPrincipalSides_pos B U basis S
local notation "sources" => allocatedPrincipalResidueSources B U basis S q hq r hsize j i

variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

theorem allocatedPrincipalResidueGridDensity_error_of_grid
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    {C ζ ε : ℝ} {M : ℕ} [NeZero M] (hC : 0 ≤ C)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε)
    (hMK : (M : ℝ) ≤ C * basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (hrows : ∀ s ∈ rows, s.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (haccuracy : (2 * positiveModerateSpectrumConstant j.val rows.card P (C / (2 * gamma)) *
        2 ^ positiveModerateSpectrumExponent j.val rows.card +
      C ^ rows.card * (2 ^ positiveModerateLengthExponent j.val * positiveModerateLengthConstant j.val P) ^
        ((layerTailDegree m + 1) * rows.card)) * ζ ≤ ε)
    (shift z : rows → ℤ) :
    ‖(((basisAxisScale (basis j) i : ℝ) ^ rows.card *
        (((allocatedPrincipalResidueJetPMF B U basis hR hσ S q hq r hsize j i rows shift).map
          (integerGridResidue M)) (integerGridResidue M z)).toReal : ℝ) : ℂ) -
      weightedModerateGridApproximation (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources
        (basisAxisScale (basis j) i) M rows (fun _ => 0) shift z
          (positiveModerateSpectrumCover rows M j.val P (C / (2 * gamma)) S.value ζ)‖ ≤
      ((basisAxisScale (basis j) i : ℝ) / M) ^ rows.card * ε := by
  exact allocatedPrincipalResidueGridDensity_error B U basis hR hσ S q hq r hsize j i hactive
    A hA P hcP hsP hC (pow_nonneg hC _) hζ hζ1 hε hMK rows hrows hB
    (allocatedGrid_modulus_cardinality B U basis S j i hgrid hC hMK rows.card)
    haccuracy shift z

end Erdos3.VectorPolynomial

end

end OAI
