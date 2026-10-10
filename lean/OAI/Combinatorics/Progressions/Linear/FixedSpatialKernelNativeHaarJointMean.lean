import OAI.Combinatorics.Progressions.Sampling.ForecastOriginalNativeHaarJointMean

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
local notation "law" => principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
local notation "single" => (fun _ : Fin m => Unit)

local notation "selected" => allocatedShortIntegerSelection U basis S.value
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {pw cw : ℝ} {Lw : ℝ≥0}
variable (Wtest : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := single) (E := Eout) (n := n) N
local notation "RawSource" => MixedCoveredJetSource I single Eout n N

section FixedSpatialKernelDensity

variable [DecidableEq X]
variable {T : Type*} [Fintype T]
variable (e : G ≃ X ⊕ (X ⊕ T)) (Wgeo Lgeo : ℝ) (z : Option G × X → ℝ)
variable (h0 : (fixedSpatialKernelBlock e Wgeo Lgeo z false).det ≠ 0)
  (h1 : (fixedSpatialKernelBlock e Wgeo Lgeo z true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
local notation "original" => fixedSpatialKernelOriginalForecastDensity
  B U basis S e Wgeo Lgeo z h0 h1 hB lower width sample

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "originalSource" => forecastDensityPhysicalChartSource B U basis S original selected
  sample x active Y N volume base physicalN τ
local notation "chart" => mixedCoveredJetChart (O := single) U o basis hb bW N
local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))

theorem fixedSpatialKernelNativeHaarMean_eq_jointMean
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a : AllocatedShortIntegerAxis U basis S.value, σ a.val.1 ≤ 1)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    {δ : ℝ} (hδ : 0 < δ)
    (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (hW : 0 ≤ Wgeo) (hL : 0 ≤ Lgeo)
    (hsize : (Fintype.card G : ℝ) * Lgeo ≤ Wgeo)
    (hz : ∀ a, |z a| ≤ 1)
    (hN : ∀ i, 0 < physicalN i) (hτ : 0 < τ)
    (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
    (hbase : base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))
    (q : ℕ) [NeZero q] (hq : q ∣ N) (hm : 0 < m)
    (hperiod : Wtest.modulus ∣ q) (hcover : Wtest.cover ∣ q) (hV : 0 < volume) :
    (forecastGeometricJacobian (X := X) (I := I) U basis R S.value volume τ : ℂ) *
      (𝔼 u ∈ integerBox physicalN,
        ∫ y, restrictedComplexChartDensity chart region 1 (originalSource u) y *
          nativeSingleSiteCoverObservable U Wtest physicalN u N y ∂haar) =
        forecastJointOriginalGridMean U basis S.value hm law active
          (forecastInactiveFixedOutput B U basis S selected
            (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
          Y N q hq volume original
          (Wtest.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
            (fun x => (base x : ℝ) / physicalN x) τ)
          (fun j => (forecastJointGridCenter U basis S.value base j : ℝ))
          (forecastJointGridScale U basis R S.value physicalN τ) := by
  have hdensity := (fixedSpatialKernelOriginalForecastDensity_bounds B U basis hR hσ S
    e Wgeo Lgeo z h0 h1 hB lower width hδ hw hl sample hs).2.continuous
  have hsupport := fixedSpatialKernelOriginalForecastDensity_zero_of_norm_gt_two
    B U basis hR hσ S e Wgeo Lgeo z h0 h1 hB lower width hδ hw hl sample hs
    hwidth hW hL hsize hz
  exact forecastNativeHaarMean_eq_jointMean B U basis S original sample x active Y N volume
    base physicalN τ o hb bW Wtest ν hR hσ hs hσ1 r hr hr3 hradius C hC hchart hbudget
    hdensity hsupport hN hτ hmargin hbase q hq hm hperiod hcover hV

end FixedSpatialKernelDensity
end Erdos3.VectorPolynomial

end

end OAI
