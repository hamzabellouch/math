import OAI.Combinatorics.Progressions.Estimates.AllocatedActualHaarComparison
import OAI.Combinatorics.Progressions.Lattices.AllocatedCoveredResidueComparison
import OAI.Combinatorics.Progressions.Linear.AllocatedKernelIdealError

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)
variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (weights : FiniteProbabilityWeights (PrincipalAxisTuples (α := α)
  (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S)))
variable (period : ℕ) (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
variable (hresidue : ∀ v, weights.weight v ≠ 0 → principalResidueLabel period v = principalResidueLabel period v₀)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod period))

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "source" => allocatedCoefficientSource B U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U b hR hσ S
local notation "reference" => allocatedLongJetReference B U b S O
local notation "density" => fun v z => allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z
local notation "root" v => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" v => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "scale" => ∏ a, allocatedLongJetOutputScale B U b S (O := O) a
local notation "proxy" => allocatedLongJetProxy B U b S x u rows s hA period residue

include hperiod hresidue

theorem allocatedPhysicalCovered_profile_comparison
    {M : ℕ} (hM : 0 < M)
    (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
    {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
    (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card
      (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
    {η ε : ℝ} (hη : 0 ≤ η)
    (hpoint : ∀ z, |weights.mean (fun v => scale * density v z) - proxy z| ≤ η)
    (g : AllocatedLongJetRows B U b S O → ℝ) (hg : Integrable g reference)
    (hprofile : (∫ z, |proxy z / scale - g z| ∂reference) ≤ ε)
    (F : AllocatedFrozenCoefficients B U b S × EuclideanJetLayers U O → ℂ)
    (hF : Measurable F) (hFb : ∀ p, ‖F p‖ ≤ 1) :
    ‖(∫ p : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
        CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d,
      weights.complexMean (fun v => F ((allocatedCoefficientSplit B U b S p.1).1,
        euclideanCoefficientJetMap U (root v) (dirs v) rows
          (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2)))
        ∂(source).prod (PMF.uniformOfFintype
          (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).toMeasure) -
      (∫ a₀, ∫ z, (g z : ℂ) *
        allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d F a₀ z ∂reference ∂frozenSource)‖ ≤
      (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) * η + ε := by
  obtain ⟨hp, hactual⟩ := allocatedLongJet_l1_comparison B U b hR hσ S x u rows s hA
    hM hi hP hMP hRP hRi hσi hcount hσ1 weights period residue hη hpoint
  have hf : Integrable (fun z => weights.mean (fun v => density v z)) reference :=
    integrable_finsetSum _ (fun v _ =>
      ((allocatedLongJetDensity_probability_data B U b hR hσ S x u v rows s hA hσ1).2.1).const_mul
        (weights.weight v))
  apply allocatedPhysicalCovered_test_comparison_of_l1 B U b hR hσ S x u v₀ rows Q hb o bW d
    s hA hσ1 weights period hperiod hresidue F g hg _ hF hFb
  exact (density_l1_triangle_le reference _ (fun z => proxy z / scale) g hf hp hg).trans
    (add_le_add hactual hprofile)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

local notation "hLayer" => layerSamplerDegree I n

theorem exists_allocated_physical_ideal_comparison
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B)
        (O := fun a : LayerSamplerAxis I n => O a.1) (α := α) hLayer
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T (ε / 2) ∧
      let t := booleanMassPerturbationScale (B := B)
        (O := fun a : LayerSamplerAxis I n => O a.1) (α := α)
        ((G × Option α) ⊕ (Σ d, SamplerCoefficientSlot G B hLayer d)) hLayer
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T m 1 (ε / 2)
      0 < t ∧ t ≤ 1 ∧
      ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
        {σ : Fin m → ℝ} (_hσ : ∀ j, 0 < σ j) (_hσt : ∀ j, σ j ≤ t)
        (S : LayerSamplerScale (G := G) B U basis R σ)
        (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
          (allocatedPrincipalSides B U basis S))
        (rows : ∀ j, O j → Finset α)
        (_hrows : ∀ j, Function.Injective (rows j))
        (_hcard : ∀ j o, (rows j o).card ≤ j.val + 1)
        (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1 ↪ B a.val)
        (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
        {M : ℕ} (_hM : 0 < M)
        (_hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
        {P : ℝ} (_hP : 0 ≤ P) (_hMP : (M : ℝ) ≤ Real.exp P)
        (_hRP : ∀ j, R j ≤ Real.exp P) (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (_hcount : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
        (modulus : ℕ)
        (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
        {mesh C : ℝ} (_hmesh0 : 0 ≤ mesh) (_hmesh1 : mesh ≤ 1)
        (_hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh) (_hC : 1 ≤ C)
        (_hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
          allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ C),
      let ideal := physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer
        (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
        (fun a => R a.1) (fun a => hR a.1) δ
      let Q := {q : (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) //
        allocatedLongIntegerCoordinate B U basis S q}
      let select := allocatedLongIntegerSelect B U basis S (O := O)
      let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), (Real.exp_pos _).le⟩
      let Kp : ℝ≥0 := (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound *
        bound ^ Fintype.card (LayerSamplerAxis I n)
      let Ki : ℝ≥0 := ‖(∏ q : (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1),
        R q.1.val.1)⁻¹‖₊ *
        (affineProductProfileLip (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) δ *
          (NNReal.mk (Real.exp P) (Real.exp_pos P).le))
      let Ro := Real.toNNReal (max (Real.exp (allocatedJetSupportLog (G := G) B α O P))
        (Real.exp P * (partitionedIdealRadius α m + 1)))
      let target := allocatedLongProfileDensity B U basis S x rows modulus residue ideal
      ∀ (v₀ : PrincipalAxisTuples (α := α)
          (fun a => ¬allocatedGridAxis (I := I) U basis S.value a) (allocatedPrincipalSides B U basis S))
        (Kcov : Fin m → Type*) [∀ j, Fintype (Kcov j)]
        (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
        (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
        (bW : ∀ j, Module.Basis (Kcov j) ℤ
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
        (d : ℕ) [NeZero d] (hσ1 : ∀ j, σ j ≤ 1)
        (weights : FiniteProbabilityWeights (PrincipalAxisTuples (α := α)
          (fun a => ¬allocatedGridAxis (I := I) U basis S.value a) (allocatedPrincipalSides B U basis S)))
        (_hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
        (_hresidue : ∀ v, weights.weight v ≠ 0 →
          principalResidueLabel modulus v = principalResidueLabel modulus v₀)
        {η : ℝ} (_hη : 0 ≤ η)
        (_hpoint : ∀ z, |weights.mean (fun v =>
          (∏ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a},
            allocatedLongJetOutputScale B U basis S (O := O) a) *
            allocatedLongJetDensity B U basis hR _hσ S x u v rows s hA hσ1 z) -
          allocatedLongJetProxy B U basis S x u rows s hA modulus residue z| ≤ η)
        (F : AllocatedFrozenCoefficients B U basis S × EuclideanJetLayers U O → ℂ),
        Measurable F → (∀ p, ‖F p‖ ≤ 1) →
      ‖(∫ p : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
          CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Kcov d,
          weights.complexMean (fun v => F ((allocatedCoefficientSplit B U basis S p.1).1,
            euclideanCoefficientJetMap U
              (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x
                (principalAxisJoin (allocatedGridAxis (I := I) U basis S.value) u v))
              (allocatedPhysicalCubeDirections B U basis S x
                (principalAxisJoin (allocatedGridAxis (I := I) U basis S.value) u v)) rows
              (canonicalCoefficientDeckSample U bW basis hb o d
                (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2)))
          ∂(allocatedCoefficientSource B U basis hR _hσ S).prod (PMF.uniformOfFintype
            (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Kcov d)).toMeasure) -
        (∫ a₀, ∫ z, (target z : ℂ) *
          allocatedCoveredFixedTest B U basis S x u v₀ rows Kcov hb o bW d F a₀ z
          ∂allocatedLongJetReference B U basis S O
          ∂allocatedFrozenCoefficientSource B U basis hR _hσ S)‖ ≤
        (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P) + 1) ^
          Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) * η +
        C ^ Fintype.card (LayerSamplerAxis I n) *
          (ε + (2 * (Ro : ℝ)) ^ Fintype.card (UnselectedColumn select) *
            ((2 * (Ro : ℝ) + 2) ^ Fintype.card Q * ((Kp : ℝ) + Ki) * mesh)) := by
  obtain ⟨δ, hδ, hδ1, hδeq, ht, ht1, hcompare⟩ := exists_allocated_long_actual_l1
    (G := G) (α := α) (O := O) B ψ hψ hrange hzero hone A T hLip hTransition hε
  refine ⟨δ, hδ, hδ1, hδeq, ht, ht1, ?_⟩
  intro J _ U basis R hR σ hσ hσt S x u rows hrows hcard block s hA
    M hM hi P hP hMP hRP hRi hσi hcount modulus residue mesh C hmesh0 hmesh1 hmesh hC hm
  have hdata := hcompare U basis hR hσ hσt S x u rows hrows hcard block s hA
    hM hi hP hMP hRP hRi hσi hcount modulus residue hmesh0 hmesh1 hmesh hC hm
  dsimp only
  intro v₀ Kcov _ hb o bW d _ hσ1 weights hperiod hresidue η hη hpoint F hF hFb
  apply allocatedPhysicalCovered_profile_comparison B U basis hR hσ S x u v₀ rows
    Kcov hb o bW d s hA hσ1 weights modulus hperiod hresidue residue
    hM hi hP hMP hRP hRi hσi hcount hη hpoint _ hdata.2.1 _ F hF hFb
  simpa only [allocatedLongProfileDensity_proxy] using hdata.2.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uCover

open MeasureTheory
open scoped NNReal Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "hLayer" => layerSamplerDegree I n
local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S O

def AllocatedGoodKernelIdealResult (selection : α ↪ G) (δ : ℝ≥0) (M : ℕ) (E : ℝ) : Prop :=
  ∃ (period : ℕ) (hperiodPos : 0 < period), period ≤ M ^ (m + 1) ∧
    (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ α) (period : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
    (∀ j : Fin m, integerScalarLattice (O j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range) ∧
    ∃ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
      (hA : ∀ j : Fin m, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ))) ∧
      ∃ hsize : ∀ a, (Fintype.card α + 1) * period ≤ principalAxisLength (fun a => ¬grid a) sides a,
      ∀ (u : PrincipalAxisTuples (α := α) grid sides)
        (r : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
          (fun a => hLayer a.val) → Option α → ZMod period),
      ∃ residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod period),
        (∀ v, (allocatedLongResidueWeights B U basis S period hperiodPos r hsize).weight v ≠ 0 → ∀ j,
          integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v) period = residue j) ∧
        ∃ v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides,
        principalResidueLabel period v₀ = r ∧
        ∀ (Kcov : Fin m → Type uCover) [∀ j, Fintype (Kcov j)]
          (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
          (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
          (bW : ∀ j, Module.Basis (Kcov j) ℤ
            (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
          (d : ℕ) [NeZero d]
          (F : AllocatedFrozenCoefficients B U basis S × EuclideanJetLayers U O → ℂ),
        Measurable F → (∀ z, ‖F z‖ ≤ 1) →
        let ideal := physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer
          grid (fun a => rows a.val.1) (fun a => R a.1) (fun a => hR a.1) δ
        let target := allocatedLongProfileDensity B U basis S x rows period residue ideal
        ‖(∫ z : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
            CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Kcov d,
            (allocatedLongResidueWeights B U basis S period hperiodPos r hsize).complexMean
              (fun v => F ((allocatedCoefficientSplit B U basis S z.1).1,
                euclideanCoefficientJetMap U
                  (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (principalAxisJoin grid u v))
                  (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u v)) rows
                  (canonicalCoefficientDeckSample U bW basis hb o d
                    (Nat.pos_of_ne_zero (NeZero.ne d)) z.1 z.2)))
            ∂(source).prod (PMF.uniformOfFintype
              (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Kcov d)).toMeasure) -
          (∫ a₀, ∫ z, (target z : ℂ) *
            allocatedCoveredFixedTest B U basis S x u v₀ rows Kcov hb o bW d F a₀ z
            ∂reference ∂frozenSource)‖ ≤ Real.exp (-E)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uGeom uCover

open MeasureTheory
open scoped ContDiff NNReal Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

local notation "hLayer" => layerSamplerDegree I n

def AllocatedPhysicalIdealAt (ε : ℝ) (δ : ℝ≥0) (t : ℝ) : Prop :=
  ∀ {J : Fin m → Type uGeom} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
    {σ : Fin m → ℝ} (_hσ : ∀ j, 0 < σ j) (_hσt : ∀ j, σ j ≤ t)
    (S : LayerSamplerScale (G := G) B U basis R σ)
    (x : G → IntegerScalarCubeBox α S.value)
    (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
      (allocatedPrincipalSides B U basis S))
    (rows : ∀ j, O j → Finset α)
    (_hrows : ∀ j, Function.Injective (rows j))
    (_hcard : ∀ j o, (rows j o).card ≤ j.val + 1)
    (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1 ↪ B a.val)
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
    {M : ℕ} (_hM : 0 < M)
    (_hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
    {P : ℝ} (_hP : 0 ≤ P) (_hMP : (M : ℝ) ≤ Real.exp P)
    (_hRP : ∀ j, R j ≤ Real.exp P) (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m, (Fintype.card
      (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
    (modulus : ℕ)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    {mesh C : ℝ} (_hmesh0 : 0 ≤ mesh) (_hmesh1 : mesh ≤ 1)
    (_hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh) (_hC : 1 ≤ C)
    (_hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ C),
  let ideal := physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer
    (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
    (fun a => R a.1) (fun a => hR a.1) δ
  let Q := {q : (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) //
    allocatedLongIntegerCoordinate B U basis S q}
  let select := allocatedLongIntegerSelect B U basis S (O := O)
  let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), (Real.exp_pos _).le⟩
  let Kp : ℝ≥0 := (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound *
    bound ^ Fintype.card (LayerSamplerAxis I n)
  let Ki : ℝ≥0 := ‖(∏ q : (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1),
    R q.1.val.1)⁻¹‖₊ *
    (affineProductProfileLip (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) δ *
      (NNReal.mk (Real.exp P) (Real.exp_pos P).le))
  let Ro := Real.toNNReal (max (Real.exp (allocatedJetSupportLog (G := G) B α O P))
    (Real.exp P * (partitionedIdealRadius α m + 1)))
  let target := allocatedLongProfileDensity B U basis S x rows modulus residue ideal
  ∀ (v₀ : PrincipalAxisTuples (α := α)
      (fun a => ¬allocatedGridAxis (I := I) U basis S.value a) (allocatedPrincipalSides B U basis S))
    (Kcov : Fin m → Type uCover) [∀ j, Fintype (Kcov j)]
    (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Kcov j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (hσ1 : ∀ j, σ j ≤ 1)
    (weights : FiniteProbabilityWeights (PrincipalAxisTuples (α := α)
      (fun a => ¬allocatedGridAxis (I := I) U basis S.value a) (allocatedPrincipalSides B U basis S)))
    (_hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (_hresidue : ∀ v, weights.weight v ≠ 0 →
      principalResidueLabel modulus v = principalResidueLabel modulus v₀)
    {η : ℝ} (_hη : 0 ≤ η)
    (_hpoint : ∀ z, |weights.mean (fun v =>
      (∏ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a},
        allocatedLongJetOutputScale B U basis S (O := O) a) *
        allocatedLongJetDensity B U basis hR _hσ S x u v rows s hA hσ1 z) -
      allocatedLongJetProxy B U basis S x u rows s hA modulus residue z| ≤ η)
    (F : AllocatedFrozenCoefficients B U basis S × EuclideanJetLayers U O → ℂ),
    Measurable F → (∀ p, ‖F p‖ ≤ 1) →
  ‖(∫ p : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
      CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Kcov d,
      weights.complexMean (fun v => F ((allocatedCoefficientSplit B U basis S p.1).1,
        euclideanCoefficientJetMap U
          (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x
            (principalAxisJoin (allocatedGridAxis (I := I) U basis S.value) u v))
          (allocatedPhysicalCubeDirections B U basis S x
            (principalAxisJoin (allocatedGridAxis (I := I) U basis S.value) u v)) rows
          (canonicalCoefficientDeckSample U bW basis hb o d
            (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2)))
      ∂(allocatedCoefficientSource B U basis hR _hσ S).prod (PMF.uniformOfFintype
        (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Kcov d)).toMeasure) -
    (∫ a₀, ∫ z, (target z : ℂ) *
      allocatedCoveredFixedTest B U basis S x u v₀ rows Kcov hb o bW d F a₀ z
      ∂allocatedLongJetReference B U basis S O
      ∂allocatedFrozenCoefficientSource B U basis hR _hσ S)‖ ≤
    (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P) + 1) ^
      Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) * η +
    C ^ Fintype.card (LayerSamplerAxis I n) *
      (ε + (2 * (Ro : ℝ)) ^ Fintype.card (UnselectedColumn select) *
        ((2 * (Ro : ℝ) + 2) ^ Fintype.card Q * ((Kp : ℝ) + Ki) * mesh))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uCover

open scoped NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

def AllocatedGoodKernelIdealAt (D E p₀ e : ℝ) (δ : ℝ≥0) (t : ℝ) : Prop :=
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * p₀
  ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
    {σ : Fin m → ℝ} (hσ : ∀ j, 0 < σ j) (_hσt : ∀ j, σ j ≤ t)
    (S : LayerSamplerScale (G := G) B U basis R σ)
    (x : G → IntegerScalarCubeBox α S.value)
    (rows : ∀ j, O j → Finset α)
    (_hinj : ∀ j, Function.Injective (rows j))
    (_hrows : ∀ j o, (rows j o).card ≤ j.val + 1)
    (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1 ↪ B a.val)
    {M : ℕ} (_hM : 0 < M) (_hMP₀ : (M : ℝ) ≤ Real.exp p₀)
    (selection : α ↪ G) (_hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
    (_hq : Fintype.card α ≤ m + 1)
    {p : ℝ} (_hp₀p : p₀ ≤ p)
    (_hRP : ∀ j, R j ≤ Real.exp p) (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p)
    (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp p)
    (_hcount : ∀ j : Fin m, (Fintype.card
      (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp p)
    (_hlarge : Real.exp (allocatedPhysicalIdealLengthEnvelope m D p e w E) ≤ S.value),
  AllocatedGoodKernelIdealResult.{uCover, _, _, _, _, _, _} (G := G) (I := I) (n := n) (J := J)
    (R := R) (σ := σ) (α := α) (O := O) B U basis hR hσ S x rows selection δ M E

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uGeom uCover

open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

def AllocatedChosenIdealAt (D E p₀ e : ℝ) (δ : ℝ≥0) (t : ℝ) : Prop :=
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * p₀
  ∀ {J : Fin m → Type uGeom} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
    {σ : Fin m → ℝ} (hσ : ∀ j, 0 < σ j) (_hσt : ∀ j, σ j ≤ t)
    {p : ℝ} (_hp₀p : p₀ ≤ p) (_hDp : D ≤ p)
    (_hRP : ∀ j, R j ≤ Real.exp p) (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p)
    (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp p),
  let S := allocatedIdealScale (G := G) B U basis hR hσ D p e w E
  (S.value : ℝ) ≤ Real.exp (allocatedIdealScaleLog m D p e w E) ∧
    ∀ (x : G → IntegerScalarCubeBox α S.value)
      (rows : ∀ j, O j → Finset α)
      (_hinj : ∀ j, Function.Injective (rows j))
      (_hrows : ∀ j o, (rows j o).card ≤ j.val + 1)
      (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1 ↪ B a.val)
      {M : ℕ} (_hM : 0 < M) (_hMP₀ : (M : ℝ) ≤ Real.exp p₀)
      (selection : α ↪ G) (_hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
      (_hq : Fintype.card α ≤ m + 1),
    AllocatedGoodKernelIdealResult.{uCover, _, _, _, _, _, _}
      (G := G) (α := α) (O := O) B U basis hR hσ S x rows selection δ M E

theorem allocatedGoodKernelIdealAt_chooseScale
    {D E p₀ e t : ℝ} {δ : ℝ≥0}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hE : 0 ≤ E) (hp₀ : 0 ≤ p₀) (he : 0 ≤ e)
    (hcompare : AllocatedGoodKernelIdealAt.{uCover, _, _, _, _, _, uGeom}
      (G := G) (α := α) (O := O) B D E p₀ e δ t) :
    AllocatedChosenIdealAt.{uGeom, uCover, _, _, _, _, _}
      (G := G) (α := α) (O := O) B D E p₀ e δ t := by
  intro J _ U basis R hR σ hσ hσt p hp₀p hDp hRP hRi hσi
  have hp : 0 ≤ p := hp₀.trans hp₀p
  have hw : 0 ≤ ((m * 2 ^ (m + 1) : ℕ) : ℝ) * p₀ := mul_nonneg (Nat.cast_nonneg _) hp₀
  refine ⟨allocatedIdealScale_upper B U basis hR hσ hdim hp he hw hE hRi hσi, ?_⟩
  intro x rows hinj hrows block M hM hMP₀ selection hx hq
  apply hcompare U basis hR hσ hσt _ x rows hinj hrows block hM hMP₀ selection hx hq
    hp₀p hRP hRi hσi
  · intro j
    exact (add_le_add ((hdim.coefficients j).trans hDp) (le_refl (1 : ℝ))).trans (Real.add_one_le_exp p)
  · exact allocatedIdealScale_lower B U basis hR hσ D p e _ E

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uGeom uCover

open MeasureTheory
open scoped ContDiff NNReal Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

local notation "hLayer" => layerSamplerDegree I n

theorem allocated_goodKernel_ideal_of_comparison
    {D E p₀ e t : ℝ} {δ : ℝ≥0}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hE : 0 ≤ E) (hp₀ : 0 ≤ p₀) (he : 0 ≤ e)
    (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e) (ht1 : t ≤ 1)
    (hcompare : AllocatedPhysicalIdealAt.{uGeom, uCover, _, _, _, _, _}
      (G := G) (α := α) (O := O) B
      (physicalIdealErrorShare E (D * ((m * 2 ^ (m + 1) : ℕ) * p₀))) δ t) :
    AllocatedGoodKernelIdealAt.{uCover, _, _, _, _, _, uGeom}
      (G := G) (α := α) (O := O) B D E p₀ e δ t := by
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * p₀
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hp₀
  have hDw : 0 ≤ D * w := mul_nonneg hdim.nonneg hw
  intro J _ U basis R hR σ hσ hσt S x rows hinj hrows block M hM hMP₀ selection hx hq
    p hp₀p hRP hRi hσi hcount hlarge
  have hp : 0 ≤ p := hp₀.trans hp₀p
  have hMP : (M : ℝ) ≤ Real.exp p := hMP₀.trans (Real.exp_le_exp.mpr hp₀p)
  have hσ1 (j) : σ j ≤ 1 := (hσt j).trans ht1
  have hs := allocatedSupportEnvelope_nonneg m hdim.nonneg hp
  have hvol : 0 ≤ allocatedIdealVolumeEnvelope m D p := by
    unfold allocatedIdealVolumeEnvelope; exact mul_nonneg hdim.nonneg (by positivity)
  have hgrid := allocatedIdealGridEnvelope_nonneg m hdim.nonneg hp he
  have hmeshCost : 0 ≤ D * w + allocatedIdealMeshEnvelope m D p e := by
    unfold allocatedIdealMeshEnvelope
    exact add_nonneg hDw (add_nonneg (mul_nonneg hdim.nonneg (by positivity)) hgrid)
  have hη := physicalIdealErrorShare_pos E (allocatedIdealVolumeEnvelope m D p)
  have hη1 := physicalIdealErrorShare_le_one hE hvol
  have hmesh0 := (physicalIdealErrorShare_pos E (D * w + allocatedIdealMeshEnvelope m D p e)).le
  have hmesh1 := physicalIdealErrorShare_le_one hE hmeshCost
  obtain ⟨hlength, hmesh⟩ := allocatedPhysicalIdealLength_spec B hdim hp he hw hE (layerTailDegree m) hlarge
  obtain ⟨period, hperiodPos, hperiodM, hspatial, hperiod, s, hA, hi, hsize, hpoint⟩ :=
    allocatedGoodKernel_prescribed_comparison B U basis hR hσ S x rows hM selection hx hq hinj hrows hσ1
      hp (show 0 ≤ E + allocatedIdealVolumeEnvelope m D p + 3 by positivity)
      hη hη1 hMP hRP hRi hσi hcount (physicalIdealErrorShare_inv E _).le hlength
  refine ⟨period, hperiodPos, hperiodM, hspatial, hperiod, s, hA, hi, hsize, ?_⟩
  intro u r
  obtain ⟨residue, hmatrix, hpoint⟩ := hpoint u r
  obtain ⟨v₀, hv₀⟩ := exists_allocatedLongResidueReference (α := α) B U basis S period hperiodPos r hsize
  have hresidue v hv :=
    (allocatedLongResidueWeights_support_label B U basis S period hperiodPos r hsize v hv).trans hv₀.symm
  have hm := fun j z => allocatedIntegerKernelMask_bound B U basis S x rows
    hM selection hx hq hinj hrows j period (residue j) z
  have hC : (1 : ℝ) ≤ layerKernelIndexBound m M := by
    exact_mod_cast Nat.succ_le_of_lt (pow_pos hM (m * 2 ^ (m + 1)))
  have hcomparison := hcompare U basis hR hσ hσt S x u rows hinj hrows block s hA
    hM hi hp hMP hRP hRi hσi hcount period residue hmesh0 hmesh1 hmesh hC hm
  refine ⟨residue, hmatrix, v₀, hv₀, ?_⟩
  intro Kcov _ hb o bW d _ F hF hFb
  have hbound := hcomparison v₀ Kcov hb o bW d hσ1
    (allocatedLongResidueWeights B U basis S period hperiodPos r hsize)
    hperiod hresidue hη.le hpoint F hF hFb
  have hbudget := allocatedKernelIdeal_error_le B U basis S hdim hp hp₀ he
    (fun j => (hR j).le) hRi hδe hMP₀ (E := E)
  dsimp only [w] at hbound hbudget ⊢
  simp only [NNReal.coe_mul, NNReal.coe_mk,
    coe_nnnorm] at hbound hbudget
  exact le_trans (α := ℝ) hbound hbudget

end Erdos3.VectorPolynomial

end

end OAI
