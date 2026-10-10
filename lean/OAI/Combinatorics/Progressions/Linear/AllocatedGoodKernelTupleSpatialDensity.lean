import OAI.Combinatorics.Progressions.Probability.AllocatedMassTupleComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

local notation "whole" => principalTupleWeights (α := α) B (layerSamplerDegree I n) sides (allocatedPrincipalSides_pos B U b S)
local notation "frozen" => allocatedFrozenTupleWeights (α := α) B U b S
local notation "long" => allocatedLongTupleWeights (α := α) B U b S

theorem allocatedGoodKernel_original_tuple_spatial_density {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P E η : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) (hη : 0 < η) (hη1 : η ≤ 1)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hηE : η⁻¹ ≤ Real.exp E)
    (hlarge : Real.exp (allocatedJointLengthLog (G := G) B α O P E) ≤ S.value) :
    ∃ (modulus : ℕ) (hm : 0 < modulus),
      let : NeZero modulus := ⟨hm.ne'⟩
      modulus ≤ M^(m+1) ∧
      (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
      (∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
        (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range) ∧
      ∃ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0),
      (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ))) ∧
      ∃ hsize : ∀ d, (Fintype.card α+1)*modulus ≤ lengths d,
      ∃ (reference : PrincipalAxisTuples (α := α) grid sides →
        (PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
          (fun a => layerSamplerDegree I n a.val) → Option α → ZMod modulus) → PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
        (residue : PrincipalAxisTuples (α := α) grid sides →
          (PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
          (fun a => layerSamplerDegree I n a.val) → Option α → ZMod modulus) → ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
        (∀ u r, principalResidueLabel modulus (reference u r) = r) ∧
        (∀ u r v, (allocatedLongResidueWeights B U b S modulus hm r hsize).weight v ≠ 0 → ∀ j,
          integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) modulus = residue u r j) ∧
        ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
        [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
        [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
        [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
        (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
        (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
        (C : Fin m → ℝ) (_hC : ∀ j, 0 ≤ C j)
        (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
        (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B α C 1 j)
        {K : Fin m → Type*} [∀ j, Fintype (K j)]
        (bW : ∀ j, Module.Basis (K j) ℤ
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
        (d : ℕ) [NeZero d]
        (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
        [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
        (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
        [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
        (g : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides → EuclideanJetLayers U O → ℝ)
        (_hg : ∀ w, Continuous (g w)) (_hg0 : ∀ w z, 0 ≤ g w z)
        (_hlaw : ∀ w, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
          (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
          (euclideanCoefficientJetMap U
            (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x w)
            (allocatedPhysicalCubeDirections B U b S x w) rows) =
          realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) (g w))
        {D N : Type*} [Fintype D] [Fintype N] [DecidableEq N]
        (c : D → N → ℤ) (index : D → N → PrincipalTupleIndex B (layerSamplerDegree I n))
        (spatialRoot : G → ℤ) (_hroot : ∀ j, |spatialRoot j| ≤ (S.value : ℤ))
        (H : D → ℝ) (Q : D → N → ℝ) (hH : ∀ t, 0 < H t) (hQ : ∀ t j, 0 < Q t j)
        {ρ ξ mesh : ℝ} (_hξ0 : 0 ≤ ξ) (_hξ1 : ξ ≤ 1)
        (_hwidth : ∀ t j, ((|c t j| : ℤ)+(sides (index t j) : ℤ) : ℝ)*Q t j ≤ ξ*H t)
        (_hρ : 0 < ρ) (_hscale : ∀ t, ρ ≤ H t/S.value) (_hscaleQ : ∀ t j, ρ ≤ Q t j)
        (_hmeshSize : smoothSpatialMeshThreshold α G N S.value ≤ ρ) (_hmesh : 0 < mesh)
        (tv : Finset (D → (Unit ⊕ α) → ℤ))
        (_htv : ∀ v ∈ tv, ∀ t i, |((spatialStar (v t) i : ℤ) : ℝ)/H t| ≤ 1)
        (point : (D → (Unit ⊕ α) → ℤ) → EuclideanJetLayers U O)
        (test : (D → (Unit ⊕ α) → ℤ) → ℂ) (_htest : ∀ v ∈ tv, ‖test v‖ ≤ 1)
        (cap : (D → (Unit ⊕ α) → ℤ) → ℝ)
        (_hcap : ∀ y v, v ∈ tv → g y (point v) ≤ cap v)
        {Z : ℝ} (_hZ : 0 < Z),
        let hSpatialPivot := goodScalarKernelTuple_spatial_det_ne_zero selection x spatialRoot
          (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hx
        let spatialScale := (∏ t, ∏ _i : Unit ⊕ α, H t : ℝ)
        let coefficientScale := ∏ a, allocatedLongJetOutputScale B U b S (O := O) a
        let chart := mixedCoveredJetChart U o b hb bW d
        let region := mixedCoveredJetRegion (O := O) (E := K) U o b d
          (fun j _ => standardLatticeClosedQuarterBox (J j))
        let spatialProxy := fun u r v => allocatedSpatialProxy B U b S u c index x spatialRoot selection
          hSpatialPivot H hH modulus r mesh v / (spatialScale : ℂ)
        let δ := smoothVectorSpatialError D N selection M S.value modulus ρ ξ mesh / spatialScale
        let proxy := fun u r => restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O K n d =>
          allocatedCoveredFixedFactor B U b hR hσ S x u (reference u r) rows K d z.1 z.2 *
            (allocatedLongJetProxy B U b S x u rows s hA modulus (residue u r)
              (fun a => coefficientJetAxisEquiv O I n z.1 a.val) / coefficientScale))
        let chartError := fun u r => restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O K n d =>
          allocatedCoveredFixedFactor B U b hR hσ S x u (reference u r) rows K d z.1 z.2 * (η / coefficientScale))
        let target := fun u r => ∑ v : tv, test v.val * (spatialProxy u r v.val * (proxy u r (point v.val) : ℂ))
        let budget := fun u r => (∑ v : tv,
          (δ * cap v.val + ‖spatialProxy u r v.val‖ * chartError u r (point v.val))) / Z
        ‖(whole).complexMean (fun y => ∑ v : tv, test v.val *
          (((allocatedOriginalSpatialOutputLaw B U b S x spatialRoot c index H Q hH hQ y v.val).toReal : ℂ) *
            (g y (point v.val) : ℂ))) / (Z : ℂ) -
          ((frozen).complexMean (fun u => ((long).fiberLaw (principalResidueLabel modulus)).complexMean
            (target u))) / (Z : ℂ)‖ ≤
          (frozen).mean (fun u => ((long).fiberLaw (principalResidueLabel modulus)).mean (budget u)) := by
  classical
  obtain ⟨modulus, hm, hdata⟩ := allocatedGoodKernel_prescribed_spatial_density B U b hR hσ S x rows
    hM selection hx hq hinj hrows hσ1 hP hE hη hη1 hMP hRP hRi hσi hcount hηE hlarge
  let : NeZero modulus := ⟨hm.ne'⟩
  rcases hdata with ⟨hmod, hspatial, hperiod, s, hA, hi, hsize, hcompare⟩
  choose reference residue href hr hcomparison using hcompare
  refine ⟨modulus, hm, hmod, hspatial, hperiod, s, hA, hi, hsize, reference, residue, href, hr, ?_⟩
  intro _ _ _ _ hb o C hC hchart hsmall K _ bW d _ μ _ _ ν _ _ g hg hg0 hlaw
    D N _ _ _ c index spatialRoot hroot H Q hH hQ ρ ξ mesh hξ0 hξ1 hwidth hρ hscale hscaleQ hmeshSize hmesh
    tv htv point test htest cap hcap Z hZ hSpatialPivot spatialScale coefficientScale chart region
    spatialProxy δ proxy chartError target budget
  apply allocatedOriginalTuple_spatial_density_comparison B U b S modulus hm hsize x spatialRoot c index H Q hH hQ
    (fun y v => g y (point v)) tv test target budget (Z : ℂ)
  intro u r
  exact hcomparison u r hb o C hC hchart hsmall bW d μ ν
    (fun w => g (principalAxisJoin grid u w)) (fun w => hg (principalAxisJoin grid u w))
    (fun w => hg0 (principalAxisJoin grid u w)) (fun w => hlaw (principalAxisJoin grid u w))
    c index spatialRoot hroot H Q hH hQ hξ0 hξ1 hwidth hρ hscale hscaleQ hmeshSize hmesh
    tv htv point test htest cap (fun w _ v hv => hcap (principalAxisJoin grid u w) v hv) hZ

end Erdos3.VectorPolynomial

end

end OAI
