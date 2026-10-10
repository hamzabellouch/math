import OAI.Combinatorics.Progressions.Estimates.AllocatedReferenceUniformError
import OAI.Combinatorics.Progressions.Fourier.NormalizedTwistSingleSiteFourierHaar
import OAI.Combinatorics.Progressions.Sampling.AllocatedGridlessProfileBound

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "quarter" => (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))

theorem allocatedCoveredProfileDensity_grid_fourier_error
    (g : (JetAmbientIndex O J → UnitAddCircle) → ℝ)
    (hvalue : ∀ w : JetAmbientIndex O J → ℝ, (∀ i, |w i| ≤ 1 / 4) →
      g (fun i => (w i : UnitAddCircle)) =
        allocatedNormalizedGridInterpolation B U b hR hσ S u rows
          (allocatedGridAmbientCoordinates B U b S o w))
    (f : AllocatedLongJetRows B U b S O → ℝ)
    {F : Type*} [Fintype F] (frequency : F → JetAmbientIndex O J → ℤ) (c : F → ℂ)
    {δ C : ℝ} (hδ : 0 ≤ δ)
    (happrox : ∀ z, ‖(g z : ℂ) -
      ∑ a, c a * ∏ i, CircleFourier.character (frequency a i • z i)‖ ≤ δ)
    (hcap : ∀ y, |allocatedGridlessCoveredProfile B U b S x u v rows hb o bW d f y| ≤ C)
    (y : EuclideanJetLayers U O) :
    ‖(allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d quarter f y : ℂ) -
      ∑ a, (c a * ∏ i, CircleFourier.character (frequency a i • coveredJetAmbientTorus U d y i)) *
        (allocatedGridlessCoveredProfile B U b S x u v rows hb o bW d f y : ℂ)‖ ≤ δ * C := by
  rw [allocatedCoveredProfileDensity_grid_factor B U b hR hσ S x u v rows hb o bW d g hvalue f]
  simp only [Complex.ofReal_mul, ← Finset.sum_mul, ← sub_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul (happrox _) (hcap y) (abs_nonneg _) hδ

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule _root_.Set _root_.OAI.Set
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

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (rows : ∀ j, O j → Finset (Fin dim))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "quarter" => (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))

theorem allocatedRefinedComplexReference_grid_fourier_error
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
    (g : frozenTuple → (JetAmbientIndex O J → UnitAddCircle) → ℝ)
    (hvalue : ∀ u (w : JetAmbientIndex O J → ℝ), (∀ i, |w i| ≤ 1 / 4) →
      g u (fun i => (w i : UnitAddCircle)) =
        allocatedNormalizedGridInterpolation B U b hR hσ S u rows
          (allocatedGridAmbientCoordinates B U b S o w))
    (f : frozenTuple → label → AllocatedLongJetRows B U b S O → ℝ)
    {F : frozenTuple → Type*} [∀ u, Fintype (F u)]
    (frequency : ∀ u, F u → JetAmbientIndex O J → ℤ) (c : ∀ u, F u → ℂ)
    (site : frozenTuple → label → EuclideanJetLayers U O → ℂ)
    (hsite : ∀ u r y, ‖site u r y‖ ≤ 1)
    {δ C Z : ℝ} (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hZ : 0 < Z)
    (happrox : ∀ u z, ‖(g u z : ℂ) -
      ∑ a, c u a * ∏ i, CircleFourier.character (frequency u a i • z i)‖ ≤ δ)
    (hcap : ∀ u r y,
      |allocatedGridlessCoveredProfile B U b S x u (reference u r) rows hb o bW d (f u r) y| ≤ C) :
    ‖allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
        B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z
        (fun u r y => (allocatedCoveredProfileDensity B U b hR hσ S x u (reference u r)
          rows hb o bW d quarter (f u r) y : ℂ) * site u r y) -
      allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
        B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z
        (fun u r y => (∑ a, (c u a * ∏ i,
          CircleFourier.character (frequency u a i • coveredJetAmbientTorus U d y i)) *
          (allocatedGridlessCoveredProfile B U b S x u (reference u r) rows hb o bW d (f u r) y : ℂ)) * site u r y)‖ ≤
      (δ * C) * coefficientTailSpatialFactor X selection M modulus W S.value / Z := by
  apply allocatedRefinedComplexReference_uniform_error
    B U b S x X hM selection hx modulus q reference N hW mesh base cells
    hτ hξ hN hq hH hbudget hmesh hperiod hmass point test htest
    _ _ (mul_nonneg hδ hC) hZ
  intro u r y
  have he := allocatedCoveredProfileDensity_grid_fourier_error
    B U b hR hσ S x u (reference u r) rows hb o bW d
    (g u) (hvalue u) (f u r) (frequency u) (c u) hδ (happrox u) (hcap u r) y
  rw [← sub_mul, norm_mul]
  exact (mul_le_mul_of_nonneg_left (hsite u r y) (norm_nonneg _)).trans
    (by simpa only [mul_one] using he)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule _root_.Set _root_.OAI.Set
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

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "rows" => (fun j : Fin m => (Subtype.val : jets j → Finset (Fin dim)))
local notation "siteIndex" => JetAmbientIndex (fun _ : Fin m => Unit) J

local notation "frozenTuple" => PrincipalAxisTuples (α := Fin dim)
  (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S)
local notation "label" => (PrincipalTupleIndex
  (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B (Subtype.val a))
  (fun a => layerSamplerDegree I n (Subtype.val a)) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q))

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "quarter" => (fun j (_ : jets j) => standardLatticeClosedQuarterBox (J j))

theorem allocatedRefinedComplexReference_site_character_error
    (hτ : 0 < τ) (hξ : 0 < ξ) (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t)
    (hH : ∀ t, 1 ≤ trimmedSpatialRootScale τ N q t)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W) (hmesh : 0 < mesh)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U jets)
    (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (htest : ∀ z, ‖test z‖ ≤ 1)
    (g : frozenTuple → (JetAmbientIndex jets J → UnitAddCircle) → ℝ)
    (hvalue : ∀ u (w : JetAmbientIndex jets J → ℝ), (∀ i, |w i| ≤ 1 / 4) →
      g u (fun i => (w i : UnitAddCircle)) =
        allocatedNormalizedGridInterpolation B U b hR hσ S u rows
          (allocatedGridAmbientCoordinates B U b S o w))
    (f : frozenTuple → label → AllocatedLongJetRows B U b S jets → ℝ)
    {F : frozenTuple → Type*} [∀ u, Fintype (F u)]
    (frequency : ∀ u, F u → JetAmbientIndex jets J → ℤ) (c : ∀ u, F u → ℂ)
    (gsite : Finset (Fin dim) → (siteIndex → UnitAddCircle) → ℂ)
    (hsite : ∀ s z, ‖gsite s z‖ ≤ 1)
    {δ C Z : ℝ} (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hZ : 0 < Z)
    (happrox : ∀ u z, ‖(g u z : ℂ) -
      ∑ a, c u a * ∏ i, CircleFourier.character (frequency u a i • z i)‖ ≤ δ)
    (hcap : ∀ u r y,
      |allocatedGridlessCoveredProfile B U b S x u (reference u r) rows hb o bW d (f u r) y| ≤ C) :
    ‖allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
        B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z
        (fun u r y => (allocatedCoveredProfileDensity B U b hR hσ S x u (reference u r)
          rows hb o bW d quarter (f u r) y : ℂ) *
          ∏ s, gsite s (coveredJetAmbientTorus U d (coveredBooleanSiteValue U y s))) -
      allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
        B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z
        (fun u r y => ∑ a, c u a *
          ((allocatedGridlessCoveredProfile B U b S x u (reference u r) rows hb o bW d (f u r) y : ℂ) *
            ∏ s, booleanCharacterSiteFactor (frequency u a) gsite s
              (coveredJetAmbientTorus U d (coveredBooleanSiteValue U y s))))‖ ≤
      (δ * C) * coefficientTailSpatialFactor X selection M modulus W S.value / Z := by
  have hunit (y : EuclideanJetLayers U jets) :
      ‖∏ s, gsite s (coveredJetAmbientTorus U d (coveredBooleanSiteValue U y s))‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun s _ => hsite s _)
  have he := allocatedRefinedComplexReference_grid_fourier_error
    B U b S x X hM selection hx modulus q reference N hW mesh base cells
    hR hσ rows hb o bW d hτ hξ hN hq hH hbudget hmesh hperiod hmass point test htest
    g hvalue f frequency c
    (fun _ _ y => ∏ s, gsite s (coveredJetAmbientTorus U d (coveredBooleanSiteValue U y s)))
    (fun _ _ y => hunit y) hδ hC hZ happrox hcap
  simpa only [← booleanCharacterSiteFactor_expansion, ambientIntegerCharacter] using he

end Erdos3.VectorPolynomial

end

end OAI
