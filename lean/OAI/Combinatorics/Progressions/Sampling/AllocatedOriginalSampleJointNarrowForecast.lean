import OAI.Combinatorics.Progressions.Estimates.AllocatedNarrowPrincipalMeanComparison
import OAI.Combinatorics.Progressions.Lattices.AllocatedOriginalSampleResidueMixtureForecast
import OAI.Combinatorics.Progressions.Linear.AllocatedKernelRootBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [DecidableEq G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "activeB" => (fun a : Active => B (Subtype.val a))
local notation "activeDegree" => (fun a : Active => degree (Subtype.val a))
local notation "Input" => PrincipalTupleIndex activeB activeDegree
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

local notation "sides" => allocatedPrincipalSides B U basis S
local notation "hSides" => allocatedPrincipalSides_pos B U basis S
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty) short sides
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Original" => PrincipalIntegerTuples B degree Empty sides
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))

local notation "vars" => LayerSamplerVariables G I n B
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

theorem allocatedOriginalSample_narrow_forecast_comparison
    (s : Empty ↪ G) (x : G → IntegerScalarCubeBox Empty S.value)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hS : 2 ≤ S.value)
    (q : ℕ) [NeZero q] (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    (τ ξ : ℝ) (box : X → ℕ)
    (hτ : 0 < τ) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hbox : ∀ t, 0 < box t)
    (modulus : X → ℕ) (hmodulus : ∀ t, 0 < modulus t)
    (r : ColumnResiduePattern (Option vars) X modulus)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus {r}
      (narrowTrimmedSpatialWidths (G := G) (J := FullInput) budget τ ξ box) z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ z : Option vars × X, (modulus z.2 : ℝ) /
      narrowTrimmedSpatialWidths (G := G) (J := FullInput) budget τ ξ box z ≤ δ)
    (hspatialSmall : (4 : ℝ) ^ Fintype.card (Option vars × X) *
      ((Fintype.card (Option vars × X) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    (coefficient : (FullInput → Option Empty → ZMod q) → ℂ)
    (hcoefficient : ∀ r, ‖coefficient r‖ ≤ 1)
    (φ : (FullInput → Option Empty → ZMod q) → ShortTuple → Domain → ℂ)
    {Kφ : ℝ≥0} (hφ : ∀ r u, LipschitzWith Kφ (φ r u))
    (hφone : ∀ r u y, ‖φ r u y‖ ≤ 1) :
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleLiftLip B U basis S
    let law := principalTupleWeights (α := Empty) B degree sides hSides
    let Pos := {r : FullInput → Option Empty → ZMod q //
      0 < law.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))}
    let hp : (selectedSpatialPivot (fun g => (x g none : ℤ))
      (scalarCubeDifferenceMatrix x) s).det ≠ 0 := by
        simp only [selectedSpatialPivot, rootDifferenceMatrix_det, Matrix.det_isEmpty, ne_eq,
          Int.one_ne_zero, not_false_eq_true]
    ‖law.complexMean (fun v => coefficient (principalResidueLabel q v) *
      (∑' z, ((selectedResidueSmoothPMF modulus {r}
        (narrowTrimmedSpatialWidths (G := G) (J := FullInput) budget τ ξ box)
        (narrowTrimmedSpatialWidths_pos (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0))
          hτ hξ box hbox) hZ z).toReal : ℂ) *
        φ (principalResidueLabel q v) (principalAxisRestrict short v)
          ((fun o : Σ _ : X, Unit ⊕ Empty =>
            (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v) z o.1 : ℝ) /
              (τ * (box o.1 : ℝ) / 8)),
            allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1)
              sample (fun j => (((principalAxisRestrict (fun a => ¬short a) v) j none : ℤ) : ℝ) / S.value)))) -
      ∑ r : Pos, (law.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r.val)) : ℂ) *
        coefficient r.val * (allocatedShortPrincipalResidueLaw B U basis S q r.val r.property).complexMean
          (fun u => ∫ y, φ r.val u y ∂realDensityMeasure volume (allocatedOriginalSampleForecastDensity (X := X)
            B U basis S s (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x) hp
              (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0))
              (by exact_mod_cast S.positive : (0 : ℝ) < S.value) hB lower width sample))‖ ≤
      (4 * (4 : ℝ) ^ Fintype.card (Option vars × X) *
        (2 * (Kφ : ℝ) + 2 * ((Fintype.card (Option vars × X) : ℝ) * probabilityProfileLipschitz)) * δ +
        (Kφ : ℝ) * ξ) +
      2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) := by
  classical
  intro lower width K law Pos hp
  let F := allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1) sample
  let value := fun (v : Original) (z : (Σ _ : X, Unit ⊕ Empty) → ℝ) =>
    φ (principalResidueLabel q v) (principalAxisRestrict short v)
      (z, F (fun j => (((principalAxisRestrict (fun a => ¬short a) v) j none : ℤ) : ℝ) / S.value))
  have hLip (v : Original) : LipschitzWith Kφ (value v) := by
    apply LipschitzWith.of_dist_le_mul
    intro z z'
    simpa only [value, Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using
      (hφ (principalResidueLabel q v) (principalAxisRestrict short v)).dist_le_mul
        (z, F (fun j => (((principalAxisRestrict (fun a => ¬short a) v) j none : ℤ) : ℝ) / S.value))
        (z', F (fun j => (((principalAxisRestrict (fun a => ¬short a) v) j none : ℤ) : ℝ) / S.value))
  have hspatial := allocatedNarrowPhysicalSpatial_principalMean_comparison B U basis S s x law
    τ ξ box hτ hξ hξ1 hbox modulus hmodulus r hZ hδ hδ1 hmesh hspatialSmall
    (fun v => coefficient (principalResidueLabel q v)) (fun v => hcoefficient _)
    value hLip (fun v z => hφone _ _ _)
  have hprincipal := allocatedOriginalSample_residue_mixture_forecast_comparison
    B U basis hR hσ S s (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x) hp
    (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0))
    (by exact_mod_cast S.positive : (0 : ℝ) < S.value) hB (allocatedKernelRoot_budget B U basis S x)
    sample hs hS q hsize hsmall coefficient hcoefficient φ hφ hφone
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hspatial hprincipal)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [DecidableEq G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "activeB" => (fun a : Active => B (Subtype.val a))
local notation "activeDegree" => (fun a : Active => degree (Subtype.val a))
local notation "Input" => PrincipalTupleIndex activeB activeDegree
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

local notation "sides" => allocatedPrincipalSides B U basis S
local notation "hSides" => allocatedPrincipalSides_pos B U basis S
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty) short sides
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Original" => PrincipalIntegerTuples B degree Empty sides
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))

local notation "vars" => LayerSamplerVariables G I n B
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

theorem allocatedOriginalSample_narrow_uniform_forecast_comparison
    (s : Empty ↪ G) (x : G → IntegerScalarCubeBox Empty S.value)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hS : 2 ≤ S.value)
    (q : ℕ) [NeZero q] (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    (τ ξ : ℝ) (box : X → ℕ)
    (hτ : 0 < τ) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hbox : ∀ t, 0 < box t)
    (modulus : X → ℕ) (hmodulus : ∀ t, 0 < modulus t)
    (r : ColumnResiduePattern (Option vars) X modulus)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus {r}
      (narrowTrimmedSpatialWidths (G := G) (J := FullInput) budget τ ξ box) z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ z : Option vars × X, (modulus z.2 : ℝ) /
      narrowTrimmedSpatialWidths (G := G) (J := FullInput) budget τ ξ box z ≤ δ)
    (hspatialSmall : (4 : ℝ) ^ Fintype.card (Option vars × X) *
      ((Fintype.card (Option vars × X) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    (coefficient : (FullInput → Option Empty → ZMod q) → ℂ)
    (hcoefficient : ∀ r, ‖coefficient r‖ ≤ 1)
    (φ : (FullInput → Option Empty → ZMod q) → ShortTuple → Domain → ℂ)
    {Kφ : ℝ≥0} (hφ : ∀ r u, LipschitzWith Kφ (φ r u))
    (hφone : ∀ r u y, ‖φ r u y‖ ≤ 1) :
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleLiftLip B U basis S
    let law := principalTupleWeights (α := Empty) B degree sides hSides
    let hp : (selectedSpatialPivot (fun g => (x g none : ℤ))
      (scalarCubeDifferenceMatrix x) s).det ≠ 0 := by
        simp only [selectedSpatialPivot, rootDifferenceMatrix_det, Matrix.det_isEmpty, ne_eq,
          Int.one_ne_zero, not_false_eq_true]
    ‖law.complexMean (fun v => coefficient (principalResidueLabel q v) *
      (∑' z, ((selectedResidueSmoothPMF modulus {r}
        (narrowTrimmedSpatialWidths (G := G) (J := FullInput) budget τ ξ box)
        (narrowTrimmedSpatialWidths_pos (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0))
          hτ hξ box hbox) hZ z).toReal : ℂ) *
        φ (principalResidueLabel q v) (principalAxisRestrict short v)
          ((fun o : Σ _ : X, Unit ⊕ Empty =>
            (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v) z o.1 : ℝ) /
              (τ * (box o.1 : ℝ) / 8)),
            allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1)
              sample (fun j => (((principalAxisRestrict (fun a => ¬short a) v) j none : ℤ) : ℝ) / S.value)))) -
      (allocatedUnconditionalShortPrincipalLaw B U basis S).complexMean (fun u =>
        (FiniteProbabilityWeights.uniform (Input → ZMod q)).complexMean (fun ar =>
          coefficient (allocatedPrincipalResidueJoin B U basis S q u ar) *
            ∫ y, φ (allocatedPrincipalResidueJoin B U basis S q u ar) u y
              ∂realDensityMeasure volume (allocatedOriginalSampleForecastDensity (X := X)
                B U basis S s (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x) hp
                  (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0))
                  (by exact_mod_cast S.positive : (0 : ℝ) < S.value) hB lower width sample)))‖ ≤
      (4 * (4 : ℝ) ^ Fintype.card (Option vars × X) *
        (2 * (Kφ : ℝ) + 2 * ((Fintype.card (Option vars × X) : ℝ) * probabilityProfileLipschitz)) * δ +
        (Kφ : ℝ) * ξ) +
      2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) +
      4 * Fintype.card Input * ((q : ℝ) / S.value) := by
  classical
  intro lower width K law hp
  let density := allocatedOriginalSampleForecastDensity (X := X)
    B U basis S s (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x) hp
    (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0))
    (by exact_mod_cast S.positive : (0 : ℝ) < S.value) hB lower width sample
  let μ := realDensityMeasure volume density
  have hSpos : (0 : ℝ) < S.value := by exact_mod_cast S.positive
  have hSreal : (2 : ℝ) ≤ S.value := by exact_mod_cast hS
  have hwidth : (1 / 2 : ℝ) ≤ ((S.value : ℝ) - 1) / S.value := by
    apply (le_div_iff₀ hSpos).mpr
    linarith
  have he := allocatedOriginalSampleForecastSource_density_of_supported (X := X)
    B U basis hR hσ S s (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x) hp
    (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)) hSpos
    hB lower width (δ := 1 / 2) (by norm_num)
    (fun _ _ => hwidth) (fun _ _ => le_rfl) sample hs
    (allocatedKernelRoot_budget B U basis S x)
  let : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (realDensityMeasure volume density)
    rw [← he]
    exact allocatedOriginalSampleForecastSource_probability B U basis S lower width
      s (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x) hp
      (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)) hSpos sample
  have hnorm (rr : FullInput → Option Empty → ZMod q) (u : ShortTuple) :
      ‖coefficient rr * ∫ y, φ rr u y ∂μ‖ ≤ 1 := by
    rw [norm_mul]
    have hi : ‖∫ y, φ rr u y ∂μ‖ ≤ 1 := by
      simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
        (μ := μ) (Filter.Eventually.of_forall (fun y => hφone rr u y))
    exact (mul_le_mul (hcoefficient rr) hi (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)
  have hactive := allocatedPrincipalResidue_mixture_active_uniform B U basis S q
    (fun rr u => coefficient rr * ∫ y, φ rr u y ∂μ) hnorm
  simp only [FiniteProbabilityWeights.complexMean_mul_left, ← mul_assoc] at hactive
  have hbase := allocatedOriginalSample_narrow_forecast_comparison B U basis hR hσ S
    s x hB sample hs hS q hsize hsmall τ ξ box hτ hξ hξ1 hbox modulus hmodulus r hZ
    hδ hδ1 hmesh hspatialSmall coefficient hcoefficient φ hφ hφone
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hbase hactive)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [DecidableEq G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "activeB" => (fun a : Active => B (Subtype.val a))
local notation "activeDegree" => (fun a : Active => degree (Subtype.val a))
local notation "Input" => PrincipalTupleIndex activeB activeDegree
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

local notation "sides" => allocatedPrincipalSides B U basis S
local notation "hSides" => allocatedPrincipalSides_pos B U basis S
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty) short sides
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Original" => PrincipalIntegerTuples B degree Empty sides
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))

local notation "vars" => LayerSamplerVariables G I n B
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

theorem allocatedOriginalSample_joint_narrow_forecast_comparison
    (s : Empty ↪ G)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hS : 2 ≤ S.value)
    (q : ℕ) [NeZero q] (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    (τ ξ : ℝ) (box : X → ℕ)
    (hτ : 0 < τ) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hbox : ∀ t, 0 < box t)
    (modulus : X → ℕ) (hmodulus : ∀ t, 0 < modulus t)
    (r : ColumnResiduePattern (Option vars) X modulus)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus {r}
      (narrowTrimmedSpatialWidths (G := G) (J := FullInput) budget τ ξ box) z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ z : Option vars × X, (modulus z.2 : ℝ) /
      narrowTrimmedSpatialWidths (G := G) (J := FullInput) budget τ ξ box z ≤ δ)
    (hspatialSmall : (4 : ℝ) ^ Fintype.card (Option vars × X) *
      ((Fintype.card (Option vars × X) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    (coefficient : (G → ZMod q) → (FullInput → Option Empty → ZMod q) → ℂ)
    (hcoefficient : ∀ rG r, ‖coefficient rG r‖ ≤ 1)
    (φ : (G → ZMod q) → (FullInput → Option Empty → ZMod q) → ShortTuple → Domain → ℂ)
    {Kφ : ℝ≥0} (hφ : ∀ rG r u, LipschitzWith Kφ (φ rG r u))
    (hφone : ∀ rG r u y, ‖φ rG r u y‖ ≤ 1) :
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleLiftLip B U basis S
    let law := principalTupleWeights (α := Empty) B degree sides hSides
    let kernel := FiniteProbabilityWeights.pi (fun _ : G =>
      integerScalarCubeWeights Empty S.value S.positive)
    let hp := fun x : G → IntegerScalarCubeBox Empty S.value =>
      (show (selectedSpatialPivot (fun g => (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) s).det ≠ 0 from by
          simp only [selectedSpatialPivot, rootDifferenceMatrix_det, Matrix.det_isEmpty, ne_eq,
            Int.one_ne_zero, not_false_eq_true])
    let density := fun x : G → IntegerScalarCubeBox Empty S.value =>
      allocatedOriginalSampleForecastDensity (X := X)
        B U basis S s (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x) (hp x)
        (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0))
        (by exact_mod_cast S.positive : (0 : ℝ) < S.value) hB lower width sample
    ‖kernel.complexMean (fun x => law.complexMean (fun v =>
      coefficient (fun g => ((x g none : ℤ) : ZMod q)) (principalResidueLabel q v) *
      (∑' z, ((selectedResidueSmoothPMF modulus {r}
        (narrowTrimmedSpatialWidths (G := G) (J := FullInput) budget τ ξ box)
        (narrowTrimmedSpatialWidths_pos (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0))
          hτ hξ box hbox) hZ z).toReal : ℂ) *
        φ (fun g => ((x g none : ℤ) : ZMod q)) (principalResidueLabel q v) (principalAxisRestrict short v)
          ((fun o : Σ _ : X, Unit ⊕ Empty =>
            (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v) z o.1 : ℝ) /
              (τ * (box o.1 : ℝ) / 8)),
            allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1)
              sample (fun j => (((principalAxisRestrict (fun a => ¬short a) v) j none : ℤ) : ℝ) / S.value))))) -
      (allocatedUnconditionalShortPrincipalLaw B U basis S).complexMean (fun u =>
        (FiniteProbabilityWeights.uniform (Input → ZMod q)).complexMean (fun ar =>
          (FiniteProbabilityWeights.uniform (G → ZMod q)).complexMean (fun rG =>
            kernel.complexMean (fun x =>
              coefficient rG (allocatedPrincipalResidueJoin B U basis S q u ar) *
                ∫ y, φ rG (allocatedPrincipalResidueJoin B U basis S q u ar) u y
                  ∂realDensityMeasure volume (density x)))))‖ ≤
      ((4 * (4 : ℝ) ^ Fintype.card (Option vars × X) *
        (2 * (Kφ : ℝ) + 2 * ((Fintype.card (Option vars × X) : ℝ) * probabilityProfileLipschitz)) * δ +
        (Kφ : ℝ) * ξ) +
      2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) +
      4 * Fintype.card Input * ((q : ℝ) / S.value)) +
      2 * ((1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ)) *
        (Fintype.card G * ((q : ℝ) / S.value))) := by
  classical
  intro lower width K law kernel hp density
  let E : ℝ := (4 * (4 : ℝ) ^ Fintype.card (Option vars × X) *
      (2 * (Kφ : ℝ) + 2 * ((Fintype.card (Option vars × X) : ℝ) * probabilityProfileLipschitz)) * δ +
      (Kφ : ℝ) * ξ) +
    2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
      ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) +
    4 * Fintype.card Input * ((q : ℝ) / S.value)
  let approximate := fun x : G → IntegerScalarCubeBox Empty S.value =>
    (allocatedUnconditionalShortPrincipalLaw B U basis S).complexMean (fun u =>
      (FiniteProbabilityWeights.uniform (Input → ZMod q)).complexMean (fun ar =>
        coefficient (fun g => ((x g none : ℤ) : ZMod q))
          (allocatedPrincipalResidueJoin B U basis S q u ar) *
        ∫ y, φ (fun g => ((x g none : ℤ) : ZMod q))
          (allocatedPrincipalResidueJoin B U basis S q u ar) u y
          ∂realDensityMeasure volume (density x)))
  have hSpos : (0 : ℝ) < S.value := by exact_mod_cast S.positive
  have hSreal : (2 : ℝ) ≤ S.value := by exact_mod_cast hS
  have hwidth : (1 / 2 : ℝ) ≤ ((S.value : ℝ) - 1) / S.value := by
    apply (le_div_iff₀ hSpos).mpr
    linarith
  have hd (x : G → IntegerScalarCubeBox Empty S.value) :
      allocatedOriginalSampleForecastSource (X := X) (W := budget) (L := (S.value : ℝ))
        B U basis S s (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x) lower width sample =
        realDensityMeasure volume (density x) :=
    allocatedOriginalSampleForecastSource_density_of_supported (X := X)
      B U basis hR hσ S s (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x) (hp x)
      (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)) hSpos
      hB lower width (δ := 1 / 2) (by norm_num)
      (fun _ _ => hwidth) (fun _ _ => le_rfl) sample hs
      (allocatedKernelRoot_budget B U basis S x)
  have hdec := allocatedJointLongForecast_weighted_residue_decoupling
    B U basis S lower width s sample q hsize hsmall
    (fun rG ar u => coefficient rG (allocatedPrincipalResidueJoin B U basis S q u ar))
    (fun rG ar u => hcoefficient rG _)
    (fun rG ar u => φ rG (allocatedPrincipalResidueJoin B U basis S q u ar) u)
    (fun rG ar u => hφ rG _ u) (fun rG ar u y => hφone rG _ u y)
  dsimp only at hdec
  simp only [hd] at hdec
  have hnarrow := (kernel.norm_complexMean_sub_le _ approximate (fun _ => E)
    (fun x _ => allocatedOriginalSample_narrow_uniform_forecast_comparison
      B U basis hR hσ S s x hB sample hs hS q hsize hsmall
      τ ξ box hτ hξ hξ1 hbox modulus hmodulus r hZ hδ hδ1 hmesh hspatialSmall
      (coefficient (fun g => ((x g none : ℤ) : ZMod q)))
      (hcoefficient (fun g => ((x g none : ℤ) : ZMod q)))
      (φ (fun g => ((x g none : ℤ) : ZMod q)))
      (hφ (fun g => ((x g none : ℤ) : ZMod q)))
      (hφone (fun g => ((x g none : ℤ) : ZMod q))))).trans_eq (kernel.mean_const E)
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hnarrow hdec)

end Erdos3.VectorPolynomial

end

end OAI
