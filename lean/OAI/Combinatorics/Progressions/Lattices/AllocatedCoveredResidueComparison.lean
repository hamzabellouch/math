import OAI.Combinatorics.Progressions.Estimates.AllocatedSlicedCoveredComparison

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
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
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
variable (period : ℕ) (hp : 0 < period)
variable (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
variable (r : PrincipalTupleIndex
  (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
  (fun a => layerSamplerDegree I n a.val) → Option α → ZMod period)
variable (hsize : ∀ j, (Fintype.card α + 1) * period ≤
  principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S) j)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod period))

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "weights" => allocatedLongResidueWeights B U b S period hp r hsize
local notation "source" => allocatedCoefficientSource B U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U b hR hσ S
local notation "reference" => allocatedLongJetReference B U b S O
local notation "density" => (fun v z => allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z)
local notation "scale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)
local notation "proxy" => allocatedLongJetProxy B U b S x u rows s hA period residue
local notation "root" v => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" v => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)

include hperiod

theorem exists_allocatedPhysicalCovered_residue_comparison
    {M : ℕ} (hM : 0 < M)
    (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
    {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
    (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ)
      + 1 ≤ Real.exp P)
    {ε : ℝ} (hε : 0 ≤ ε) (he : ∀ z, |(weights).mean (fun v => scale * density v z) - proxy z| ≤ ε) :
    ∃ v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides,
      principalResidueLabel period v₀ = r ∧
      ∀ F : AllocatedFrozenCoefficients B U b S × EuclideanJetLayers U O → ℂ,
      Measurable F → (∀ p, ‖F p‖ ≤ 1) →
      ‖(∫ p, (weights).complexMean (fun v => F (((allocatedCoefficientSplit B U b S) p.1).1,
          euclideanCoefficientJetMap U (root v) (dirs v) rows
            (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2)))
            ∂(source).prod (deck).toMeasure) -
        ∫ a₀, ∫ z, ((proxy z / scale : ℝ) : ℂ) *
          allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d F a₀ z ∂reference ∂frozenSource‖ ≤
        (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P) + 1) ^
          Fintype.card (Σ a : LayerSamplerAxis I n, O (Sigma.fst a)) * ε := by
  obtain ⟨v₀, hv₀⟩ := exists_allocatedLongResidueReference (α := α) B U b S period hp r hsize
  refine ⟨v₀, hv₀, ?_⟩
  intro F hF hbound
  have hres : ∀ v, (weights).weight v ≠ 0 → principalResidueLabel period v = principalResidueLabel period v₀ := by
    intro v hv
    exact (allocatedLongResidueWeights_support_label B U b S period hp r hsize v hv).trans hv₀.symm
  exact allocatedPhysicalCovered_test_comparison B U b hR hσ S x u v₀ rows Q hb o bW d
    s hA hσ1 weights period hperiod hres F residue hM hi hP hMP hRP hRi hσi hcount hε he hF hbound

end Erdos3.VectorPolynomial

end

end OAI
