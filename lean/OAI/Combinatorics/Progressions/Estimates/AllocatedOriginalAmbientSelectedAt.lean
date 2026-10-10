import OAI.Combinatorics.Progressions.Estimates.AllocatedCommonWeightedOriginal
import OAI.Combinatorics.Progressions.Estimates.AllocatedUnitSiteFactors

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j => (Subtype.val : jets j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "output" => (Σ a : {a // ¬grid a}, jets (Sigma.fst (Subtype.val a)))
local notation "volume" => (∏ q : output, R (Sigma.fst (Subtype.val (Sigma.fst q))))

variable (X : Type*) [Fintype X]
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  ∀ j, Matrix (BoundedBooleanJet (Fin dim) (j.val + 1)) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Module.Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) →
  EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1)))
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (Z : ℝ)

local notation "region" => (fun j (_ : jets j) => standardLatticeClosedQuarterBox (J j))
local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

theorem allocatedRefinedIdealReference_finite_site_error
    {T : Type*} [Fintype T] (c : T → ℂ)
    (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε D P E : ℝ} (hε : 0 ≤ ε)
    (haccuracy : ε ≤ siteReferenceAccuracy m D P E) (hZ : 1 / 2 ≤ Z)
    (hsupport : ∀ i s w, (∃ a, 2 * idealSiteBoxRadius (Fin dim) m < |w a|) → f i s w = 0)
    (he : ∀ z : AllocatedLongJetRows B U b S jets,
      ‖(physicalActiveProfileIdeal (G := G) (B := B) (G × Option (Fin dim)) (layerSamplerDegree I n) grid
          (fun a => (Subtype.val : jets a.val.1 → Finset (Fin dim)))
          (fun a => R a.1) (fun a => hR a.1) δ (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
        (∑ i, c i * ∏ s, f i s (allocatedIdealSiteCoordinates B U b S z s)) / ((volume : ℝ) : ℂ)‖ ≤
        ε / volume)
    (hmass : ∀ u r, (∑ t : cells × window,
      ‖allocatedRefinedProfileCoefficient (τ := τ) (ξ := ξ) B U b S x X hM selection hx modulus q
        reference N hW mesh base cells test u r t‖ *
      |allocatedCoveredProfileDensity B U b hR hσ S x u (reference u r) jetRows hb o bW d region
        (allocatedLongProfileDensity B U b S x jetRows modulus (residue u r) (allocatedSiteBuffer B U b S))
        (point (allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells u r t.1 t.2.val))|) ≤
      Real.exp (siteReferenceMassLog m D P)) :
    ‖allocatedRefinedIdealReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x jetRows X hM selection hx modulus q reference residue hb o bW d
        N hW mesh base cells point test Z δ -
      ∑ i, c i * allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
        B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z
        (fun u r => allocatedCoveredComplexProfileDensity B U b hR hσ S x u (reference u r) jetRows hb o bW d region
          (allocatedSiteTermDensity B U b S x modulus (residue u r) (f i)))‖ ≤ Real.exp (-E) := by
  rw [allocatedRefinedIdealReference_as_complex, ← allocatedRefinedComplexReference_sum]
  have hZ0 : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hbound := allocatedRefinedComplexReference_pointwise_error (τ := τ) (ξ := ξ)
    B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z
    (fun u r y => (allocatedRefinedIdealProfile B U b hR hσ S x jetRows X modulus q reference residue hb o bW d δ u r y : ℂ))
    (fun u r y => ∑ i, c i * allocatedCoveredComplexProfileDensity B U b hR hσ S x u (reference u r) jetRows hb o bW d region
      (allocatedSiteTermDensity B U b S x modulus (residue u r) (f i)) y)
    (fun u r y => |allocatedCoveredProfileDensity B U b hR hσ S x u (reference u r) jetRows hb o bW d region
      (allocatedLongProfileDensity B U b S x jetRows modulus (residue u r) (allocatedSiteBuffer B U b S)) y|)
    hε hZ0 (fun u r y => ?_) hmass
  · exact hbound.trans (siteReference_error_le m haccuracy hZ)
  · exact allocatedCoveredIdealSiteApproximation_error B U b hR hσ S x u (reference u r) hb o bW d
      modulus (residue u r) c f δ hδ hδ1 hε hsupport he y

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j => (Subtype.val : jets j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "output" => (Σ a : {a // ¬grid a}, jets (Sigma.fst (Subtype.val a)))
local notation "volume" => (∏ q : output, R (Sigma.fst (Subtype.val (Sigma.fst q))))

variable (X : Type*) [Fintype X]
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  ∀ j, Matrix (BoundedBooleanJet (Fin dim) (j.val + 1)) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Module.Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) →
  EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1)))
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (Z : ℝ)

local notation "region" => (fun j (_ : jets j) => standardLatticeClosedQuarterBox (J j))
local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

theorem exists_allocated_refined_ideal_site_approximation
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ε p D P E : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hbox : ((m : ℝ) + 2) * Fintype.card (Fin dim) + 3 ≤ p)
    (hεp : ε⁻¹ ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p)
    (haccuracy : ε ≤ siteReferenceAccuracy m D P E) (hZ : 1 / 2 ≤ Z)
    (hmass : ∀ test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ,
      (∀ w, ‖test w‖ ≤ 1) → ∀ u r, (∑ t : cells × window,
      ‖allocatedRefinedProfileCoefficient (τ := τ) (ξ := ξ) B U b S x X hM selection hx modulus q
        reference N hW mesh base cells test u r t‖ *
      |allocatedCoveredProfileDensity B U b hR hσ S x u (reference u r) jetRows hb o bW d region
        (allocatedLongProfileDensity B U b S x jetRows modulus (residue u r) (allocatedSiteBuffer B U b S))
        (point (allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells u r t.1 t.2.val))|) ≤
      Real.exp (siteReferenceMassLog m D P)) :
    let radius : ℝ≥0 := ⟨idealSiteBoxRadius (Fin dim) m, (idealSiteBoxRadius_pos (Fin dim) m).le⟩
    let C : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * radius)
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1)) (Fintype.card (Fin dim)) p
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) : ℝ) ≤
        Real.exp ((Fintype.card (Finset (Fin dim)) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ i, ‖a i‖) ≤ Real.exp ((Fintype.card (Finset (Fin dim)) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q) ∧
        (∀ i s v, ‖f i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + C) (f i s)) ∧
        (∀ i s v, (∃ d, 2 * idealSiteBoxRadius (Fin dim) m < |v d|) → f i s v = 0) ∧
        ∀ test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ, (∀ w, ‖test w‖ ≤ 1) →
    ‖allocatedRefinedIdealReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x jetRows X hM selection hx modulus q reference residue hb o bW d
        N hW mesh base cells point test Z δ -
      ∑ i, a i * allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
        B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z
        (fun u r => allocatedCoveredComplexProfileDensity B U b hR hσ S x u (reference u r) jetRows hb o bW d region
          (allocatedSiteTermDensity B U b S x modulus (residue u r) (f i)))‖ ≤ Real.exp (-E) := by
  intro radius C Q
  obtain ⟨k, hk, hcard, a, f, ha, hf, hLf, hsupport, herr⟩ :=
    exists_allocated_ideal_site_approximation (α := Fin dim) B U b S hR δ hδ hδ1 hε hp hbox hεp hδp
  refine ⟨k, hk, hcard, a, f, ha, hf, hLf, hsupport, ?_⟩
  intro test htest
  exact allocatedRefinedIdealReference_finite_site_error B U b hR hσ S x X hM selection hx modulus q
    reference residue hb o bW d N hW mesh base cells point test Z a f δ hδ hδ1 hε.le haccuracy hZ
    hsupport (fun z => (herr z).2) (hmass test htest)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j => (Subtype.val : jets j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "output" => (Σ a : {a // ¬grid a}, jets (Sigma.fst (Subtype.val a)))
local notation "volume" => (∏ q : output, R (Sigma.fst (Subtype.val (Sigma.fst q))))

variable (X : Type*) [Fintype X]
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  ∀ j, Matrix (BoundedBooleanJet (Fin dim) (j.val + 1)) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Module.Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) →
  EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1)))
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (Z : ℝ)

local notation "region" => (fun j (_ : jets j) => standardLatticeClosedQuarterBox (J j))
local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

theorem allocatedRefinedUnitSiteReference_eq
    (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hinv : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ Cinv j * ‖w‖)
    (hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv
      (allocatedSiteRootAllowance (Fin dim) m) j)
    (f : Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
    (hsupport : ∀ s w, (∃ a, 2 * idealSiteBoxRadius (Fin dim) m < |w a|) → f s w = 0)
    (g : Finset (Fin dim) → (JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) → ℂ)
    (hvalue : ∀ s (w : JetAmbientIndex (fun _ : Fin m => Unit) J → ℝ),
      (∀ a, |w a| ≤ 1 / 4) → 2 * g s (fun a => (w a : UnitAddCircle)) =
        f s (allocatedAmbientSiteCoordinates B U b S o w)) :
    allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
      B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z
      (fun u r => allocatedCoveredComplexProfileDensity B U b hR hσ S x u (reference u r)
        jetRows hb o bW d region (allocatedSiteTermDensity B U b S x modulus (residue u r) f)) =
    (2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
      allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
        B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z
        (fun u r y => (allocatedCoveredProfileDensity B U b hR hσ S x u (reference u r)
          jetRows hb o bW d region (allocatedMaskedSiteEnvelope B U b S x modulus (residue u r)) y : ℂ) *
          ∏ s, g s (coveredJetAmbientTorus U d (coveredBooleanSiteValue U y s))) := by
  have heq : (fun u r => allocatedCoveredComplexProfileDensity B U b hR hσ S x u (reference u r)
      jetRows hb o bW d region (allocatedSiteTermDensity B U b S x modulus (residue u r) f)) =
      (fun u r y => (2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
        ((allocatedCoveredProfileDensity B U b hR hσ S x u (reference u r)
          jetRows hb o bW d region (allocatedMaskedSiteEnvelope B U b S x modulus (residue u r)) y : ℂ) *
          ∏ s, g s (coveredJetAmbientTorus U d (coveredBooleanSiteValue U y s)))) := by
    funext u r y
    simpa only [mul_assoc] using allocatedCoveredSiteTerm_unit_ambient_factorization
      B U b hR hσ S x u (reference u r) hb o bW d hσ1 Cinv hCinv hinv hsmall
      modulus (residue u r) f hsupport g hvalue y
  rw [heq]
  exact allocatedRefinedComplexReference_const_mul (τ := τ) (ξ := ξ)
    B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z _ _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uG uI uB uGeom uCover uSpace

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {dim : ℕ}

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

def AllocatedOriginalAmbientSelectedAt (D Psp E e t : ℝ) (A T Kproj Kideal Kbuf : ℕ) : Prop :=
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
  let error := allocatedReferenceIdealError m D Psp (E + 1 + 4)
  let gainLog := allocatedProfileGainLog m D Psp w
  ∀ (_hmPsp : ((m + 1 : ℕ) : ℝ) ≤ Psp) (_hdimPsp : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (_hGPsp : (Fintype.card G : ℝ) ≤ Psp)
    (_hvarsGrowth : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp Psp)
    {J : Fin m → Type uGeom} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (_hσt : ∀ j, σ j ≤ t)
    {pNum : ℝ} (_hPspNum : Psp ≤ pNum) (_hDNum : D ≤ pNum)
    (_herrorNum : profileReferenceErrorLog Psp (E + 1 + 4) ≤ pNum)
    (_hRefineNum : (m + 1 : ℕ) * Psp + Psp ^ 2 + (dim + 1 : ℕ) ≤ pNum)
    (_hRP : ∀ j, R j ≤ Real.exp pNum) (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp pNum)
    (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp pNum)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (C : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp pNum),
  let S := allocatedIdealScale (G := G) B U b hR hσ D pNum e w error
  let lengthLog := allocatedIdealScaleLog m D pNum e w error
  let Pbase := allocatedIdealSourceBudget m D pNum e w error
  let l := allocatedSpatialLateLog (G := G) B Pbase Pbase
  let F := allocatedProfileFourierOutput (allocatedActualProfileInput m D pNum e gainLog lengthLog)
  let Fbuf := allocatedProfileFourierOutput
    (allocatedSiteBufferInput m D pNum (allocatedSiteEnvelopeGain m D Psp) lengthLog (normalizedSiteCutoffBound : ℝ))
  let Q := allocatedSourceSamplingBudget m dim A Pbase (E + 1) l (F + Fbuf)
  let K := max Kbuf (max T (max Kproj Kideal))
  let pSite := allocatedSiteApproximationInput m dim D Psp E e
  let Qsite := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1)) (Fintype.card (Fin dim)) pSite
  let radius : ℝ≥0 := ⟨idealSiteBoxRadius (Fin dim) m, (idealSiteBoxRadius_pos (Fin dim) m).le⟩
  let Ccut : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * radius)
  (S.value : ℝ) ≤ Real.exp lengthLog ∧
  ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Qsite + 8) ∧
    (Fintype.card (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) : ℝ) ≤
      Real.exp ((Fintype.card (Finset (Fin dim)) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Qsite + 8)) ∧
    ∃ (a : (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → ℂ)
      (g : (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → Finset (Fin dim) →
        (JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) → ℂ),
      (∑ i, ‖a i‖) ≤ Real.exp ((Fintype.card (Finset (Fin dim)) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Qsite + 8) + Qsite + Fintype.card (Finset (Fin dim))) ∧
      (∀ i s v, ‖g i s v‖ ≤ 1) ∧
      (∀ i s, LipschitzWith
        ((⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Qsite + 12), Real.exp_nonneg _⟩ + Ccut) *
          ⟨Real.exp (4 * pNum), Real.exp_nonneg _⟩) (g i s)) ∧
  ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {Mk : ℕ} (hMk : 0 < Mk) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (_hqDim : dim ≤ m + 1) (_hMkPsp : (Mk : ℝ) ≤ Real.exp Psp),
  ∃ (d : ℕ) (hd : 0 < d),
    let : NeZero d := ⟨hd.ne'⟩
    (d : ℝ) ≤ Real.exp ((Pbase + A) ^ A) ∧
  ∃ (modulus : ℕ) (hmodulus : 0 < modulus),
    let : NeZero modulus := ⟨hmodulus.ne'⟩
    modulus ≤ Mk ^ (m + 1) ∧
    (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
    (∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range) ∧
    ∃ (s : ∀ j, jets j ↪ BoundedIntegerExponent G (j.val + 1))
      (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (jetRows j)).submatrix id (s j)).det ≠ 0),
    (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (jetRows j) (s j) (hA j) (1 / (Mk : ℝ))) ∧
    ∀ (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, jets a.val.1 ↪ B a.val)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)] [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Kcov : Fin m → Type uCover} [∀ j, Fintype (Kcov j)]
    (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (V : Fin m → ℝ≥0)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hVp : ∀ j, (V j : ℝ) ≤ Real.exp pNum)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv (allocatedSiteRootAllowance (Fin dim) m) j)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {X : Type uSpace} [Fintype X] [DecidableEq X]
    (_hXPsp : (Fintype.card X : ℝ) ≤ Psp)
    (q : X → ℕ) (_hq : ∀ t, 0 < q t) (_hqPsp : ∀ t, (q t : ℝ) ≤ Real.exp Psp),
    let refined := residueRefinedPeriod modulus q
    ∃ hRefined : 0 < refined,
    let : NeZero refined := ⟨hRefined.ne'⟩
    (∀ t, q t * modulus ∣ refined) ∧
    (refined : ℝ) ≤ Real.exp ((m + 1 : ℕ) * Psp + Fintype.card X * Psp) ∧
    ∃ hsize : ∀ a, (Fintype.card (Fin dim) + 1) * refined ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
        (allocatedPrincipalSides B U b S) a,
    ∃ (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
    (∀ u r, principalResidueLabel refined (reference u r) = r) ∧
    (∀ u r v, (allocatedLongResidueWeights B U b S refined hRefined r hsize).weight v ≠ 0 →
      ∀ j, integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u jetRows j v) modulus = residue u r j) ∧
    let W := allocatedPhysicalRootBudget B U b S (fun _ => 0)
    let hW := allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
    let indices := PrincipalTupleIndex B (layerSamplerDegree I n)
    let ξ := normalizedTupleNarrowWidth X indices selection Mk Psp (E + 1 + 2)
    let hξ := normalizedTupleNarrowWidth_pos X indices selection Mk Psp (E + 1 + 2)
    let mesh := normalizedTupleRadius X selection Mk Psp (E + 1 + 2) W / 4
    ∀ {τ : ℝ} (hτ : 0 < τ) (_hτP : 1 / τ ≤ Real.exp pNum)
    (N : X → ℕ) (hN : ∀ t, 0 < N t)
    (_hsize : ∀ t, Real.exp ((Q + K) ^ K) ≤ (N t : ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    {rank : ℝ}
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) rank (U j) (poly j))
    (_hRank : Real.exp ((Q + K) ^ K) ≤ rank)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hcells : cells.Nonempty)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (_htest : ∀ site v, ‖test site v‖ ≤ 1)
    (Z : ℝ) (_hZ : 1 / 2 ≤ Z),
    ∃ hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := indices) W τ ξ N) z,
    ‖allocatedOriginalTupleSource B U b hR hσ S x X q hb o N hN hW hτ hξ base cells hmass
        (physicalCubeSiteTest test) Z poly hmem -
      ∑ i, a i * allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
        B U b S x X hMk selection hx modulus q reference N hW mesh base cells
        (physicalCubeEuclideanSample U d poly hmem) (physicalCubeSiteTest test) Z
        (fun u r y =>
          (allocatedCoveredProfileDensity B U b hR hσ S x u (reference u r)
            jetRows hb o bW d (fun j _ => standardLatticeClosedQuarterBox (J j))
            (allocatedMaskedSiteEnvelope B U b S x modulus (residue u r)) y : ℂ) *
          ∏ s, g i s (coveredJetAmbientTorus U d (coveredBooleanSiteValue U y s)))‖ ≤
      Real.exp (-E)

end Erdos3.VectorPolynomial

end

end OAI
