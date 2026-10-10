import OAI.Combinatorics.Progressions.Probability.AllocatedReferenceCoefficientMass

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (X : Type*) [Fintype X]
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
    (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S))
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))

variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "frozenTuple" => PrincipalAxisTuples (α := Fin dim)
  (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S)
local notation "label" => (PrincipalTupleIndex
  (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B (Subtype.val a))
  (fun a => layerSamplerDegree I n (Subtype.val a)) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q))

omit [∀ j, Fintype (O j)] in
theorem allocatedRefinedComplexReference_uniform_error
    (hτ : 0 < τ) (hξ : 0 < ξ) (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t)
    (hH : ∀ t, 1 ≤ trimmedSpatialRootScale τ N q t)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W) (hmesh : 0 < mesh)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
    (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (htest : ∀ z, ‖test z‖ ≤ 1)
    (f g : frozenTuple → label → EuclideanJetLayers U O → ℂ)
    {ε Z : ℝ} (hε : 0 ≤ ε) (hZ : 0 < Z)
    (he : ∀ u r y, ‖f u r y - g u r y‖ ≤ ε) :
    ‖allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
        B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z f -
      allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
        B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z g‖ ≤
      ε * coefficientTailSpatialFactor X selection M modulus W S.value / Z := by
  apply allocatedRefinedComplexReference_pointwise_error
    B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z
    f g (fun _ _ _ => 1) hε hZ
  · intro u r y
    simpa only [mul_one] using he u r y
  · intro u r
    simpa only [mul_one] using allocatedRefinedProfileCoefficient_mass
      B U b S x X hM selection hx modulus q reference N hW mesh base cells
      hτ hξ hN hq hH hbudget hmesh hperiod hmass test htest u r

end Erdos3.VectorPolynomial

end

end OAI
