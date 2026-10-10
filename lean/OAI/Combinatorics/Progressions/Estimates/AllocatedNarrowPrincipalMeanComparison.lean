import OAI.Combinatorics.Progressions.Geometry.AllocatedNarrowSpatialCanonicalComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [DecidableEq G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "principal" => PrincipalTupleIndex B (layerSamplerDegree I n)
local notation "vars" => LayerSamplerVariables G I n B
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

local notation "Original" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)
local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)

theorem allocatedNarrowPhysicalSpatial_principalMean_comparison
    (s : Empty ↪ G) (x : G → IntegerScalarCubeBox Empty S.value)
    (p : FiniteProbabilityWeights Original)
    (τ ξ : ℝ) (box : X → ℕ)
    (hτ : 0 < τ) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hbox : ∀ t, 0 < box t)
    (modulus : X → ℕ) (hmodulus : ∀ t, 0 < modulus t)
    (r : ColumnResiduePattern (Option vars) X modulus)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus {r}
      (narrowTrimmedSpatialWidths (G := G) (J := principal) budget τ ξ box) z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ z : Option vars × X, (modulus z.2 : ℝ) /
      narrowTrimmedSpatialWidths (G := G) (J := principal) budget τ ξ box z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (Option vars × X) *
      ((Fintype.card (Option vars × X) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    (coefficient : Original → ℂ) (hcoef : ∀ y, ‖coefficient y‖ ≤ 1)
    (φ : Original → Spatial → ℂ) {A : ℝ≥0}
    (hLip : ∀ y, LipschitzWith A (φ y)) (hφ : ∀ y z, ‖φ y z‖ ≤ 1) :
    ‖p.complexMean (fun y => coefficient y *
      (∑' z, ((selectedResidueSmoothPMF modulus {r}
        (narrowTrimmedSpatialWidths (G := G) (J := principal) budget τ ξ box)
        (narrowTrimmedSpatialWidths_pos (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0))
          hτ hξ box hbox) hZ z).toReal : ℂ) *
        φ y (fun o : Σ _ : X, Unit ⊕ Empty =>
          (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y) z o.1 : ℝ) /
            (τ * (box o.1 : ℝ) / 8)))) -
      ∫ z, p.complexMean (fun y => coefficient y * φ y z)
        ∂canonicalZeroSpatialLaw s (fun g => (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) budget (S.value : ℝ)‖ ≤
      4 * (4 : ℝ) ^ Fintype.card (Option vars × X) *
        (2 * (A : ℝ) + 2 * ((Fintype.card (Option vars × X) : ℝ) * probabilityProfileLipschitz)) * δ +
      (A : ℝ) * ξ := by
  classical
  let μ := canonicalZeroSpatialLaw (X := X) s (fun g => (x g none : ℤ))
    (scalarCubeDifferenceMatrix x) budget (S.value : ℝ)
  have hpivot : (selectedSpatialPivot (fun g => (x g none : ℤ))
      (scalarCubeDifferenceMatrix x) s).det ≠ 0 := by
    simp only [selectedSpatialPivot, rootDifferenceMatrix_det, Matrix.det_isEmpty, ne_eq,
      Int.one_ne_zero, not_false_eq_true]
  let := canonicalZeroSpatialLaw_probability (X := X) s (fun g => (x g none : ℤ))
    (scalarCubeDifferenceMatrix x) hpivot
    (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0))
    (by exact_mod_cast S.positive : (0 : ℝ) < S.value)
  have hint (y : Original) : Integrable (φ y) μ :=
    ⟨(hLip y).continuous.measurable.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall (hφ y))⟩
  have he := p.integral_complexMean μ (fun z y => coefficient y * φ y z)
    (fun y => (hint y).const_mul _)
  simp only [integral_const_mul] at he
  rw [he]
  apply (p.norm_complexMean_sub_le _ _ (fun _ =>
      4 * (4 : ℝ) ^ Fintype.card (Option vars × X) *
        (2 * (A : ℝ) + 2 * ((Fintype.card (Option vars × X) : ℝ) * probabilityProfileLipschitz)) * δ +
      (A : ℝ) * ξ) ?_).trans_eq (p.mean_const _)
  intro y _
  rw [← mul_sub, norm_mul]
  have h := allocatedNarrowPhysicalSpatial_canonical_comparison B U basis S s x y τ ξ box
    hτ hξ hξ1 hbox modulus hmodulus r hZ hδ hδ1 hmesh hsmall (φ y) (hLip y) (hφ y)
  calc
    _ ≤ 1 * ‖_‖ := mul_le_mul_of_nonneg_right (hcoef y) (norm_nonneg _)
    _ ≤ _ := by simpa only [one_mul] using h

end Erdos3.VectorPolynomial

end

end OAI
