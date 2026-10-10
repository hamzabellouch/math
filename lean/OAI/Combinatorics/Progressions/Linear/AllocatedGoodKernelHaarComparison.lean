import OAI.Combinatorics.Progressions.Estimates.AllocatedCoveredHaarTransfer
import OAI.Combinatorics.Progressions.Estimates.AllocatedPrescribedCoveredComparison
import OAI.Combinatorics.Progressions.Estimates.CoveredJetSampleMeasurable
import OAI.Combinatorics.Progressions.Probability.AllocatedMassTupleComparison

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

local notation "FrozenTuples" => PrincipalAxisTuples (α := α) grid sides
local notation "LongTuples" => PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides
local notation "Labels" => (fun modulus : ℕ =>
  (PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a))
    (fun a => layerSamplerDegree I n (Subtype.val a)) → Option α → ZMod modulus))
local notation "whole" => principalTupleWeights B (layerSamplerDegree I n) sides
  (allocatedPrincipalSides_pos B U b S)
local notation "frozen" => allocatedFrozenTupleWeights (α := α) B U b S
local notation "long" => allocatedLongTupleWeights (α := α) B U b S

theorem allocatedGoodKernel_covered_tuple_comparison {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
    (hq : Fintype.card α ≤ m + 1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j t, (rows j t).card ≤ j.val + 1) (hσ1 : ∀ j, σ j ≤ 1)
    {P E η : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) (hη : 0 < η) (hη1 : η ≤ 1)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ)
      + 1 ≤ Real.exp P)
    (hηE : η⁻¹ ≤ Real.exp E)
    (hlarge : Real.exp (allocatedJointLengthLog (G := G) B α O P
      (allocatedJetTestLog (G := G) B α O P E)) ≤ S.value) :
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
      letI : NeZero period := ⟨hp.ne'⟩
      ∃ (residue : FrozenTuples → Labels period →
          ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod period))
        (v₀ : FrozenTuples → Labels period → LongTuples),
        (∀ u r v, (allocatedLongResidueWeights B U b S period hp r hsize).weight v ≠ 0 → ∀ j,
          integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) period = residue u r j) ∧
        (∀ u r, principalResidueLabel period (v₀ u r) = r) ∧
        ∀ F : FrozenTuples → Labels period →
          AllocatedFrozenCoefficients B U b S × EuclideanJetLayers U O → ℂ,
        (∀ u r, Measurable (F u r)) → (∀ u r p, ‖F u r p‖ ≤ 1) →
        ‖(∫ p, (whole).complexMean (fun y =>
            F (principalAxisRestrict grid y)
              (principalResidueLabel period (principalAxisRestrict (fun a => ¬grid a) y))
              (((allocatedCoefficientSplit B U b S) p.1).1,
                euclideanCoefficientJetMap U
                  (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
                  (allocatedPhysicalCubeDirections B U b S x y) rows
                  (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2)))
                    ∂(source).prod (deck).toMeasure) -
          (frozen).complexMean (fun u => ((long).fiberLaw (principalResidueLabel period)).complexMean
            (fun r => ∫ a₀, ∫ z,
              ((allocatedLongJetProxy B U b S x u rows s hA period (residue u r) z / scale : ℝ) : ℂ) *
                allocatedCoveredFixedTest B U b S x u (v₀ u r) rows Q hb o bW d (F u r) a₀ z
                  ∂reference ∂frozenSource))‖ ≤ η := by
  obtain ⟨period, hp, hpM, hspatial, hperiod, s, hA, hi, hsize, hcompare⟩ :=
    allocatedGoodKernel_prescribed_covered_comparison B U b hR hσ S x rows Q hb o bW d
      hM selection hx hq hinj hrows hσ1 hP hE hη hη1 hMP hRP hRi hσi hcount hηE hlarge
  let : NeZero period := ⟨hp.ne'⟩
  choose residue hmatrix v₀ hv₀ htest using hcompare
  refine ⟨period, hp, hpM, hspatial, hperiod, s, hA, hi, hsize,
    residue, v₀, hmatrix, hv₀, ?_⟩
  intro F hF hbound
  let : IsProbabilityMeasure source := allocatedCoefficientSource_probability B U b hR hσ S
  let f := fun (p : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
      CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
      (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides) =>
    F (principalAxisRestrict grid y)
      (principalResidueLabel period (principalAxisRestrict (fun a => ¬grid a) y))
      (((allocatedCoefficientSplit B U b S) p.1).1,
        euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) rows
          (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2))
  have hf (y) : Integrable (fun p => f p y) ((source).prod (deck).toMeasure) := by
    apply Integrable.of_bound (C := 1)
    · exact ((hF _ _).comp
        ((((allocatedCoefficientSplit B U b S).measurable.comp measurable_fst).fst).prodMk
          (canonicalCoefficientDeckSample_jet_measurable U o
            (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) rows b hb bW d))).aestronglyMeasurable
    · exact ae_of_all _ (fun p => hbound _ _ _)
  apply allocatedTuple_integral_comparison B U b S period hp hsize
    ((source).prod (deck).toMeasure) f hf
  intro u r
  have he := htest u r (F u r) (hF u r) (hbound u r)
  convert he using 2
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  apply (allocatedLongResidueWeights B U b S period hp r hsize).complexMean_congr_support
  intro v hv
  dsimp only [f]
  rw [principalAxisRestrict_join_left, principalAxisRestrict_join_right,
    allocatedLongResidueWeights_support_label B U b S period hp r hsize v hv]

end Erdos3.VectorPolynomial

end

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
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides
local notation "source" => allocatedCoefficientSource B U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U b hR hσ S
local notation "reference" => allocatedLongJetReference B U b S O
local notation "scale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)

local notation "FrozenTuples" => PrincipalAxisTuples (α := α) grid sides
local notation "LongTuples" => PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides
local notation "Labels" => (fun modulus : ℕ =>
  (PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a))
    (fun a => layerSamplerDegree I n (Subtype.val a)) → Option α → ZMod modulus))
local notation "whole" => principalTupleWeights B (layerSamplerDegree I n) sides
  (allocatedPrincipalSides_pos B U b S)
local notation "frozen" => allocatedFrozenTupleWeights (α := α) B U b S
local notation "long" => allocatedLongTupleWeights (α := α) B U b S

local notation "density" => (fun a => allocatedCoefficientDensity B U b hb o hR hσ S
  (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d a))
local notation "jetHaar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "physicalJet" => (fun y => euclideanCoefficientJetMap U
  (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
  (allocatedPhysicalCubeDirections B U b S x y) rows)
local notation "sample" => (fun p : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
  CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d =>
  canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) (Prod.fst p) (Prod.snd p))

theorem allocatedGoodKernel_haar_comparison {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
    (hq : Fintype.card α ≤ m + 1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j t, (rows j t).card ≤ j.val + 1) (hσ1 : ∀ j, σ j ≤ 1)
    {P E η : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) (hη : 0 < η) (hη1 : η ≤ 1)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ)
      + 1 ≤ Real.exp P)
    (hηE : η⁻¹ ≤ Real.exp E)
    (hlarge : Real.exp (allocatedJointLengthLog (G := G) B α O P
      (allocatedJetTestLog (G := G) B α O P E)) ≤ S.value)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) :
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
      letI : NeZero period := ⟨hp.ne'⟩
      ∃ (residue : FrozenTuples → Labels period →
          ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod period))
        (v₀ : FrozenTuples → Labels period → LongTuples),
        (∀ u r v, (allocatedLongResidueWeights B U b S period hp r hsize).weight v ≠ 0 → ∀ j,
          integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) period = residue u r j) ∧
        (∀ u r, principalResidueLabel period (v₀ u r) = r) ∧
        ∀ F : FrozenTuples → Labels period → EuclideanJetLayers U O → ℂ,
        (∀ u r, Measurable (F u r)) → (∀ u r z, ‖F u r z‖ ≤ 1) →
        let test := fun (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides)
          (z : EuclideanJetLayers U O) => F (principalAxisRestrict grid y)
            (principalResidueLabel period (principalAxisRestrict (fun a => ¬grid a) y)) z
        let target := (frozen).complexMean (fun u =>
          ((long).fiberLaw (principalResidueLabel period)).complexMean
            (fun r => ∫ a₀, ∫ z,
              ((allocatedLongJetProxy B U b S x u rows s hA period (residue u r) z / scale : ℝ) : ℂ) *
                allocatedCoveredFixedTest B U b S x u (v₀ u r) rows Q hb o bW d
                  (fun p => F u r p.2) a₀ z ∂reference ∂frozenSource))
        (‖(∫ a, (density a : ℂ) * (whole).complexMean (fun y => test y (physicalJet y a)) ∂μ) -
          target‖ ≤ η) ∧
        ∀ g : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides → EuclideanJetLayers U O → ℝ,
        (∀ y, Measurable (g y)) → (∀ y z, 0 ≤ g y z) →
        (∀ y, (realDensityMeasure μ density).map (physicalJet y) = realDensityMeasure jetHaar (g y)) →
        ‖(whole).complexMean (fun y => ∫ z, (g y z : ℂ) * test y z ∂jetHaar) - target‖ ≤ η := by
  obtain ⟨period, hp, hpM, hspatial, hperiod, s, hA, hi, hsize, residue, v₀, hmatrix, hv₀, hcompare⟩ :=
    allocatedGoodKernel_covered_tuple_comparison B U b hR hσ S x rows Q hb o bW d
      hM selection hx hq hinj hrows hσ1 hP hE hη hη1 hMP hRP hRi hσi hcount hηE hlarge
  let : NeZero period := ⟨hp.ne'⟩
  refine ⟨period, hp, hpM, hspatial, hperiod, s, hA, hi, hsize,
    residue, v₀, hmatrix, hv₀, ?_⟩
  intro F hF hbound test target
  have hsource : ‖(∫ p, (whole).complexMean (fun y => test y (physicalJet y (sample p)))
      ∂(source).prod (deck).toMeasure) - target‖ ≤ η :=
    hcompare (fun u r p => F u r p.2) (fun u r => (hF u r).comp measurable_snd)
      (fun u r p => hbound u r p.2)
  have htest (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides) :
      Measurable (test y) := hF _ _
  have hjet (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides) :
      Measurable (physicalJet y) :=
    (euclideanCoefficientJetMap_continuous (K := LayerSamplerVariables G I n B) U _ _ rows).measurable
  constructor
  · have he := allocatedCoveredHaar_finite_mean B U b hb o hR hσ S Q bW d μ ν
      hσ1 C hC hchart hsmall whole (fun y a => test y (physicalJet y a))
      (fun y => (htest y).comp (hjet y))
    rwa [he] at hsource
  · intro g hg hg0 hlaw
    have he := allocatedCoveredDensity_finite_mean B U b hb o hR hσ S Q bW d μ ν
      hσ1 C hC hchart hsmall whole (fun y a => physicalJet y a) hjet jetHaar
      g hg hg0 hlaw test htest (fun y z => hbound _ _ z)
    rwa [he] at hsource

end Erdos3.VectorPolynomial

end

end OAI
