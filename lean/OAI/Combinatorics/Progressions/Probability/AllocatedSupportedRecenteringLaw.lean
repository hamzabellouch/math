import OAI.Combinatorics.Progressions.Geometry.AllocatedSupportedRecentering

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
    (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S))
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

variable (hq : ∀ t, 0 < q t) (hN : ∀ t, 0 < N t) (hτ : 0 < τ)
variable (href : ∀ u r, principalResidueLabel (residueRefinedPeriod modulus q) (reference u r) = r)
variable (Q : ℝ≥0) (hQ : 1 ≤ Q) (hratio : (1 + W) / (S.value : ℝ) ≤ Q)
variable (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
variable (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
  pivotFullImage
    (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
    (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
variable (hmesh : 0 < mesh) {ε : ℝ} (hε : 0 ≤ ε) (hmargin : (3 + 2 * mesh) + 2 * ε ≤ 4)
variable (hsize : ∀ t, Fintype.card (Option (LayerSamplerVariables G I n B)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ ε * trimmedSpatialRootScale τ N q t)
variable (htest : ∀ v, ‖test v‖ ≤ 1)

local notation "shiftError" => Fintype.card X *
  ((modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
    (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Q) * (8 * mesh + ε)) *
  (1 + (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
    anisotropicSpatialDensityCap selection (1 / (M : ℝ)))^Fintype.card X

include hq hN hτ href hQ hratio hbudget hperiod hmesh hε hmargin hsize htest in
theorem allocatedResidueWeightedReference_recenter_error_law
    (law : FiniteProbabilityWeights fullTuple)
    (hwhole : ∀ y : fullTuple, law.weight y ≠ 0 →
      principalResidueLabel refined (wholeReference (principalResidueLabel refined y)) =
        principalResidueLabel refined y)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (Z : ℝ) (hZ : 0 < Z) :
    ‖law.complexMean
        (allocatedResidueWeightedProfileTerm (τ := τ) (ξ := ξ)
          B U b S x X hM selection hx modulus q reference N hW mesh base cells point test profile) / (Z : ℂ) -
      law.complexMean
        (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
          B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile) / (Z : ℂ)‖ ≤
      shiftError * law.mean
        (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
          B U b S X modulus q wholeReference x N base cells point profile) / Z := by
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_of_nonneg hZ.le]
  apply div_le_div_of_nonneg_right _ hZ.le
  have h := law.norm_complexMean_sub_le
    (allocatedResidueWeightedProfileTerm (τ := τ) (ξ := ξ)
      B U b S x X hM selection hx modulus q reference N hW mesh base cells point test profile)
    (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile)
    (fun y => shiftError * allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point profile y)
    (fun y hy => by
      have hwy := hwhole y hy
      rw [allocatedResidueWeightedProfileTerm_translate_at B U b S X modulus q reference wholeReference x
        hM selection hx N hW mesh base cells point test hq href profile y hwy]
      apply allocatedTranslatedProfileTerm_recenter_error_at <;> assumption)
  simpa only [FiniteProbabilityWeights.mean_const_mul] using h

end Erdos3.VectorPolynomial

end

end OAI
