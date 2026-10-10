import OAI.Combinatorics.Progressions.Geometry.AllocatedCanonicalSpatialProxy
import OAI.Combinatorics.Progressions.Lattices.AllocatedResidueSpatialDensity

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "rootAt" => (fun w => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u w))
local notation "dirsAt" => (fun w => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u w))
local notation "axis" => coefficientJetAxisEquiv O I n
local notation "scale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)

variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B α C 1 j)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (g : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S) → EuclideanJetLayers U O → ℝ)
variable (hg : ∀ w, Continuous (g w)) (hg0 : ∀ w z, 0 ≤ g w z)
variable (hlaw : ∀ w, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
    (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
    (euclideanCoefficientJetMap U
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u w))
      (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u w)) rows) =
    realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) (g w))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := O) (E := E) U o b d
  (fun j _ => standardLatticeClosedQuarterBox (J j))

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

open BooleanCubeKernel
variable [DecidableEq G]

local notation "physicalVars" => LayerSamplerVariables G I n B
local notation "kernelRoot" => (fun g => (0 : ℤ) + (x g none : ℤ))

include hσ1 hC hchart hsmall hg hg0 hlaw in
theorem allocatedAnisotropic_spatial_density_comparison
    (selection : α ↪ G) {M : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (hx : GoodScalarKernelTuple selection κ M x)
    (modulus : ℕ) [NeZero modulus] (hm : 0 < modulus)
    (label : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
      (fun a => layerSamplerDegree I n a.val) → Option α → ZMod modulus)
    (hsize : ∀ t, (Fintype.card α + 1) * modulus ≤ principalAxisLength (fun a => ¬grid a) sides t)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (hv₀ : principalResidueLabel modulus v₀ = label)
    (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    {ε : ℝ} (hpoint : ∀ z, |(allocatedLongResidueWeights B U b S modulus hm label hsize).mean
      (fun w => scale * allocatedLongJetDensity B U b hR hσ S x u w rows s hA hσ1 z) -
        allocatedLongJetProxy B U b S x u rows s hA modulus residue z| ≤ ε)
    {X : Type*} [Fintype X] (N q : X → ℕ)
    (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t)
    {W τ C₀ ρ ξ mesh : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hρ : 0 < ρ)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hprincipalRoot : ∀ j, (sides j : ℝ) ≤ ξ * (1 + W))
    (hprincipalDir : ∀ j, (sides j : ℝ) ≤ ξ * S.value)
    (hphysicalSize : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ τ * (N t : ℝ))
    (hmeshSize : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
    (hspatialPeriod : integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot kernelRoot (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns kernelRoot (scalarCubeDifferenceMatrix x) selection))
    (hmesh : 0 < mesh)
    (point : (X → (Unit ⊕ α) → ℤ) → EuclideanJetLayers U O)
    (test : (X → (Unit ⊕ α) → ℤ) → ℂ)
    (htest : ∀ v ∈ commonSpatialWindow (trimmedSpatialRootScale τ N q), ‖test v‖ ≤ 1)
    (cap : (X → (Unit ⊕ α) → ℤ) → ℝ)
    (hcap : ∀ w, (allocatedLongResidueWeights B U b S modulus hm label hsize).weight w ≠ 0 →
      ∀ v ∈ commonSpatialWindow (trimmedSpatialRootScale τ N q), g w (point v) ≤ cap v)
    {Z : ℝ} (hZ : 0 < Z) :
    let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x kernelRoot hκ hx
    let Vphys := trimmedSpatialWidths (K := physicalVars) W τ N
    let hVphys := trimmedSpatialWidths_pos (K := physicalVars) hW hτ N hN
    let Qwidth := residueProfileWidth q Vphys
    let hQwidth := residueProfileWidth_pos q Vphys hq hVphys
    let H := trimmedSpatialRootScale τ N q
    let T := trimmedSpatialSlopeScale W τ N q
    let volume := ∏ t, ∏ i, physicalSpatialOutputScale α (H t) (T t) S.value i
    let spatialProxy := fun v => allocatedCanonicalSpatialProxy B U b S (fun _ => 0) x u
      selection hp H W hW modulus label mesh v / (volume : ℂ)
    let δ := anisotropicVectorSiteError X (PrincipalTupleIndex B (layerSamplerDegree I n))
      selection M modulus W κ C₀ ρ ξ mesh / volume
    let proxy := restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O E n d =>
      allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows E d z.1 z.2 *
        (allocatedLongJetProxy B U b S x u rows s hA modulus residue (fun a => axis z.1 a.val) / scale))
    let error := restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O E n d =>
      allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows E d z.1 z.2 * (ε / scale))
    ‖(allocatedLongResidueWeights B U b S modulus hm label hsize).complexMean
        (fun w => ∑ v : commonSpatialWindow H, test v.val *
          (((allocatedCenteredSpatialLaw B U b S (fun _ => 0) x u Qwidth hQwidth w v.val).toReal : ℂ) *
            (g w (point v.val) : ℂ))) / (Z : ℂ) -
      (∑ v : commonSpatialWindow H, test v.val * (spatialProxy v.val * (proxy (point v.val) : ℂ))) /
        (Z : ℂ)‖ ≤
      (∑ v : commonSpatialWindow H, (δ * cap v.val + ‖spatialProxy v.val‖ * error (point v.val))) / Z := by
  intro hp Vphys hVphys Qwidth hQwidth H T volume spatialProxy δ proxy error
  have hH (t) : 0 < H t := (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).1
  have hT (t) : 0 < T t := (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).2
  have hvolume : 0 < volume := Finset.prod_pos (fun t _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos α (hH t) (hT t) (Nat.cast_pos.mpr S.positive) i))
  have hvolumeC : (volume : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hvolume.ne'
  have hδ : 0 ≤ δ := div_nonneg
    (anisotropicVectorSiteError_nonneg X _ selection M modulus hW hκ.le
      (zero_le_one.trans hC₀) hρ.le hξ0 hmesh.le) hvolume.le
  have hspatial (w) (hw : (allocatedLongResidueWeights B U b S modulus hm label hsize).weight w ≠ 0)
      (v : commonSpatialWindow H) :
      ‖((allocatedCenteredSpatialLaw B U b S (fun _ => 0) x u Qwidth hQwidth w v.val).toReal : ℂ) -
        spatialProxy v.val‖ ≤ δ := by
    have he := allocatedTrimmedSpatial_fiber_site_error B U b S (fun _ => 0) x u selection N q hN hq
      hW hτ hκ hρ hx hbudget hC₀ hLC hWC hξ0 hξ1
      (fun j => by simpa using hprincipalRoot j) (fun j => by simpa using hprincipalDir j)
      hphysicalSize hmeshSize modulus hspatialPeriod hmesh label w
      (allocatedLongResidueWeights_support_label B U b S modulus hm label hsize w hw) v.val v.property
    have hid (a : ℝ) (z : ℂ) : (a : ℂ) - z / (volume : ℂ) =
        (((volume * a : ℝ) : ℂ) - z) / (volume : ℂ) := by
      rw [Complex.ofReal_mul, sub_div, mul_div_cancel_left₀ _ hvolumeC]
    change ‖((allocatedCenteredSpatialLaw B U b S (fun _ => 0) x u Qwidth hQwidth w v.val).toReal : ℂ) -
      _ / (volume : ℂ)‖ ≤ δ
    rw [hid, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hvolume]
    exact div_le_div_of_nonneg_right he hvolume.le
  exact allocatedResidue_spatial_density_comparison B U b hR hσ S x u rows s hA
    hb o hσ1 C hC hchart hsmall bW d μ ν g hg hg0 hlaw modulus hm label hsize v₀ hv₀ hperiod residue hpoint
    (fun v : commonSpatialWindow H => point v.val)
    (fun w (v : commonSpatialWindow H) =>
      ((allocatedCenteredSpatialLaw B U b S (fun _ => 0) x u Qwidth hQwidth w v.val).toReal : ℂ))
    (fun v : commonSpatialWindow H => spatialProxy v.val)
    (fun v : commonSpatialWindow H => test v.val) (fun _ => δ)
    (fun v : commonSpatialWindow H => cap v.val) (fun _ => hδ)
    (fun v => htest v.val v.property) hspatial (fun w hw v => hcap w hw v.val v.property) hZ

end Erdos3.VectorPolynomial

end

end OAI
