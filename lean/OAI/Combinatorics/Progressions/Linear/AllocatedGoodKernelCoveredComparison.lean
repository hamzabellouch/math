import OAI.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions
import OAI.Combinatorics.Progressions.Lattices.AllocatedCoveredResidueComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val + 1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides
local notation "source" => allocatedCoefficientSource B U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U b hR hσ S
local notation "reference" => allocatedLongJetReference B U b S O
local notation "scale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)

theorem allocatedGoodKernel_covered_comparison {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
    (hq : Fintype.card α ≤ m + 1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j t, (rows j t).card ≤ j.val + 1) (hσ1 : ∀ j, σ j ≤ 1)
    {P E η : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) (hη : 0 < η) (hη1 : η ≤ 1)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ)
      + 1 ≤ Real.exp P)
    (hηE : η⁻¹ ≤ Real.exp E)
    (hlarge : Real.exp (allocatedJointLengthLog (G := G) B α O P E) ≤ S.value) :
    ∃ (period : ℕ) (hp : 0 < period), period ≤ M ^ (m + 1) ∧
      (∀ c : G → ℤ, integerScalarLattice (Unit ⊕ α) (period : ℤ) ≤
        pivotFullImage (selectedSpatialPivot c (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns c (scalarCubeDifferenceMatrix x) selection)) ∧
      (∀ j, integerScalarLattice (O j) (period : ℤ) ≤
        (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range) ∧
      ∃ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ))) ∧
      ∃ hsize : ∀ t, (Fintype.card α + 1) * period ≤ lengths t,
      ∀ (u : PrincipalAxisTuples (α := α) grid sides)
        (r : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
          (fun a => layerSamplerDegree I n a.val) → Option α → ZMod period),
      ∃ residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod period),
        (∀ v, (allocatedLongResidueWeights B U b S period hp r hsize).weight v ≠ 0 → ∀ j,
          integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) period = residue j) ∧
        ∃ v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides,
          principalResidueLabel period v₀ = r ∧
          ∀ F : AllocatedFrozenCoefficients B U b S × EuclideanJetLayers U O → ℂ,
          Measurable F → (∀ p, ‖F p‖ ≤ 1) →
          ‖(∫ p, (allocatedLongResidueWeights B U b S period hp r hsize).complexMean (fun v =>
              F (((allocatedCoefficientSplit B U b S) p.1).1,
                euclideanCoefficientJetMap U
                  (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v))
                  (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) rows
                  (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2)))
                ∂(source).prod (deck).toMeasure) -
            ∫ a₀, ∫ z,
              ((allocatedLongJetProxy B U b S x u rows s hA period residue z / scale : ℝ) : ℂ) *
                allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d F a₀ z ∂reference ∂frozenSource‖ ≤
            (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P) + 1) ^
              Fintype.card (Σ a : LayerSamplerAxis I n, O (Sigma.fst a)) * η := by
  obtain ⟨period, hp, hpM, hspatial, hperiod, s, hA, hi, hsize, hcompare⟩ :=
    allocatedGoodKernel_prescribed_comparison B U b hR hσ S x rows hM selection hx hq hinj hrows hσ1
      hP hE hη hη1 hMP hRP hRi hσi hcount hηE hlarge
  refine ⟨period, hp, hpM, hspatial, hperiod, s, hA, hi, hsize, ?_⟩
  intro u r
  obtain ⟨residue, hmatrix, he⟩ := hcompare u r
  obtain ⟨v₀, hv₀, htest⟩ := exists_allocatedPhysicalCovered_residue_comparison B U b hR hσ S x u
    rows Q hb o bW d s hA hσ1 period hp hperiod r hsize residue
    hM hi hP hMP hRP hRi hσi hcount hη.le he
  exact ⟨residue, hmatrix, v₀, hv₀, htest⟩

end Erdos3.VectorPolynomial

end

end OAI
