import OAI.Combinatorics.Progressions.Sampling.ForecastNativeRawSpatialFamily

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short
local notation "hamin" => unitProfilePrincipalLowerBound_pos B

variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
  (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

local notation "density" => fixedSpatialKernelOriginalForecastDensity B U basis S e W L z h0 h1 hB lower width

variable {δ : ℝ} (hδ : 0 < δ)
  (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

variable (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
variable (hW : 0 ≤ W) (hL : 0 ≤ L) (hsize : (Fintype.card G : ℝ) * L ≤ W)
variable (hz : ∀ a, |z a| ≤ 1)
include hR hσ hδ hw hl hs hwidth hW hL hsize hz

theorem fixedSpatialKernelOriginalForecastDensity_nonzero_norm_le_two
    (y : Domain) (hy : density sample y ≠ 0) : ‖y‖ ≤ 2 := by
  apply le_of_not_gt
  intro h
  exact hy (fixedSpatialKernelOriginalForecastDensity_zero_of_norm_gt_two
    B U basis hR hσ S e W L z h0 h1 hB lower width hδ hw hl sample hs
    hwidth hW hL hsize hz y h)

theorem fixedSpatialKernelOriginalForecastDensity_nonzero_spatial_bounds
    (y : Domain) (hy : density sample y ≠ 0) (i : X) :
    |y.1 ⟨i, .inl ()⟩| ≤ 2 := by
  have hn := fixedSpatialKernelOriginalForecastDensity_nonzero_norm_le_two
    B U basis hR hσ S e W L z h0 h1 hB lower width hδ hw hl sample hs
    hwidth hW hL hsize hz y hy
  exact (Real.norm_eq_abs _).symm ▸
    (norm_le_pi_norm y.1 ⟨i, .inl ()⟩).trans ((le_max_left _ _).trans hn)

theorem fixedSpatialKernelOriginalForecastDensity_nonzero_active_bounds
    (y : Domain) (hy : density sample y ≠ 0) (a : Output) :
    |y.2 a| ≤ 2 := by
  have hn := fixedSpatialKernelOriginalForecastDensity_nonzero_norm_le_two
    B U basis hR hσ S e W L z h0 h1 hB lower width hδ hw hl sample hs
    hwidth hW hL hsize hz y hy
  exact (Real.norm_eq_abs _).symm ▸
    (norm_le_pi_norm y.2 a).trans ((le_max_right _ _).trans hn)

theorem fixedSpatialKernelOriginalForecastDensity_active_bound_three :
    ∀ y, density sample y ≠ 0 → ∀ a, |y.2 a| ≤ 3 := by
  intro y hy a
  exact (fixedSpatialKernelOriginalForecastDensity_nonzero_active_bounds
    B U basis hR hσ S e W L z h0 h1 hB lower width hδ hw hl sample hs
    hwidth hW hL hsize hz y hy a).trans (by norm_num)

variable (physicalN : X → ℕ) (hN : ∀ i, 0 < physicalN i)
variable {τ : ℝ} (hτ : 0 < τ)
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
variable (base : X → ℤ) (hbase : base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))
include hN hτ hmargin hbase

theorem fixedSpatialKernelOriginalForecastDensity_zero_outside_integerBox
    (u : X → ℤ) (a : Output → ℝ) (hu : u ∉ integerBox physicalN) :
    density sample ((fun i => ((u i.1 : ℝ) - base i.1) / (τ * physicalN i.1 / 8)), a) = 0 :=
  translatedForecastDensity_zero_outside_integerBox (density sample)
    (fixedSpatialKernelOriginalForecastDensity_nonzero_spatial_bounds
      B U basis hR hσ S e W L z h0 h1 hB lower width hδ hw hl sample hs
      hwidth hW hL hsize hz)
    physicalN hN hτ hmargin base hbase u a hu

variable (xref : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {pw cw : ℝ} {Lw : ℝ≥0}
variable (Wtest : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)

theorem forecastNativeRawSpatialFamily_fixedSpatial_zero_outside
    (u : X → ℤ) (hu : u ∉ integerBox physicalN)
    (a : MixedCoveredJetSource I (fun _ => Unit) Eout n N) :
    forecastNativeRawSpatialFamily B U basis S (density sample) sample xref active Y N volume
      base physicalN τ o hb bW Wtest u a = 0 := by
  unfold forecastNativeRawSpatialFamily forecastDensityPhysicalChartSource
    forecastDensityPhysicalDeckSource
  rw [fixedSpatialKernelOriginalForecastDensity_zero_outside_integerBox
    B U basis hR hσ S e W L z h0 h1 hB lower width hδ hw hl sample hs
    hwidth hW hL hsize hz physicalN hN hτ hmargin base hbase u _ hu,
    Complex.ofReal_zero, zero_mul, zero_mul]

end Erdos3.VectorPolynomial

end

end OAI
