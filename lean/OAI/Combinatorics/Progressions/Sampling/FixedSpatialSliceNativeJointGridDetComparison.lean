import OAI.Combinatorics.Progressions.Sampling.AllocatedFixedPathRecoveredJointGridComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
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

variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (lowerG widthG : G → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
  (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hwG : ∀ g, widthG g ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lowerP widthP : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

local notation "frame" => fixedSpatialKernelSliceFrame W L z lowerG widthG
local notation "h0slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lowerG widthG false h0 hwG
local notation "h1slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lowerG widthG true h1 hwG
local notation "A₀" => fixedSpatialKernelBlockEquiv e W L frame false h0slice
local notation "A₁" => fixedSpatialKernelBlockEquiv e W L frame true h1slice

local notation "density" => fixedSpatialKernelSliceOriginalForecastDensity B U basis S e W L z
  lowerG widthG h0 h1 hwG hB lowerP widthP

variable {δP : ℝ} (hδP : 0 < δP)
  (hwP : ∀ a p, δP ≤ widthP a p) (hlP : ∀ a p, 0 ≤ lowerP a p)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

include hR hσ hδP hwP hlP hs in
theorem fixedSpatialKernelSliceOriginalForecastDensity_bounds_of_det
    {H κ0 κ1 δG : ℝ} (hH : 0 ≤ H) (hκ0 : 0 < κ0) (hκ1 : 0 < κ1) (hδG : 0 < δG)
    (hentry : ∀ i j, |fixedSpatialKernelBlock e W L z false i j| ≤ H)
    (hdet0 : κ0 ≤ |(fixedSpatialKernelBlock e W L z false).det|)
    (hdet1 : κ1 ≤ |(fixedSpatialKernelBlock e W L z true).det|)
    (hmin : ∀ g, δG ≤ widthG g) (hmax : ∀ g, widthG g ≤ 1) :
    let Csp : ℝ≥0 := Real.toNNReal ((κ1 * δG ^ Fintype.card X)⁻¹)
    let Ksp : ℝ≥0 := 2 * (Fintype.card X : ℝ≥0) * Csp *
      Real.toNNReal (Fintype.card X * ((Fintype.card X).factorial *
        H ^ (Fintype.card X - 1) / (κ0 * δG ^ Fintype.card X)))
    (∀ y, density sample y ∈ Set.Icc (0 : ℝ)
      (Csp * allocatedForecastAllAxisLiftCap B hδP)) ∧
    LipschitzWith (allocatedForecastAllAxisLiftCap B hδP * Ksp +
      Csp * allocatedForecastAllAxisLiftLip B hδP) (density sample) := by
  exact fixedSpatialKernelOriginalForecastDensity_bounds_of_det B U basis hR hσ S
    e W L frame h0slice h1slice hB lowerP widthP hδP hwP hlP sample hs
    hH (mul_pos hκ0 (pow_pos hδG _)) (mul_pos hκ1 (pow_pos hδG _))
    (fixedSpatialKernelBlock_slice_entry_bound e W L z lowerG widthG hentry
      (fun g => ⟨hδG.le.trans (hmin g), hmax g⟩))
    (fixedSpatialKernelBlock_slice_det_lower e W L z lowerG widthG false hδG hmin hdet0)
    (fixedSpatialKernelBlock_slice_det_lower e W L z lowerG widthG true hδG hmin hdet1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Original" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Joint" => X ⊕ AllocatedActiveIntegerAxis U basis S.value
local notation "Cont" => (Σ j : Fin m, I j)

include hR hσ in
theorem fixedSpatialSliceNativeJointGridMean_comparison_of_det
    (e : G ≃ X ⊕ (X ⊕ T)) (rootBudget rootLength : ℝ) (z : Option G × X → ℝ)
    (h0 : (fixedSpatialKernelBlock e rootBudget rootLength z false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e rootBudget rootLength z true).det ≠ 0)
    (lowerG widthG : G → ℝ) (hwG : ∀ g, widthG g ≠ 0)
    (hlG : ∀ g, 0 ≤ lowerG g) (hcontainedG : ∀ g, lowerG g + widthG g ≤ 1)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (lowerP widthP : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    {δP : ℝ} (hδP : 0 < δP) (hwP : ∀ a p, δP ≤ widthP a p)
    (hlP : ∀ a p, 0 ≤ lowerP a p)
    (hwidthP : ∀ a p, |lowerP a p| + |widthP a p| ≤ 1)
    {H κ0 κ1 δG : ℝ} (hH : 0 ≤ H) (hκ0 : 0 < κ0) (hκ1 : 0 < κ1) (hδG : 0 < δG)
    (hentry : ∀ i j, |fixedSpatialKernelBlock e rootBudget rootLength z false i j| ≤ H)
    (hdet0 : κ0 ≤ |(fixedSpatialKernelBlock e rootBudget rootLength z false).det|)
    (hdet1 : κ1 ≤ |(fixedSpatialKernelBlock e rootBudget rootLength z true).det|)
    (hmin : ∀ g, δG ≤ widthG g) (hmax : ∀ g, widthG g ≤ 1)
    (hW : 0 ≤ rootBudget) (hL : 0 ≤ rootLength)
    (hsize : (Fintype.card G : ℝ) * rootLength ≤ rootBudget)
    (hz : ∀ a, |z a| ≤ 1)
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hm : 0 < m)
    (τ : ℝ) (base : X → ℤ) (box : X → ℕ)
    (xref : G → IntegerScalarCubeBox Empty S.value)
    {Ω : Type*} [Fintype Ω]
    (law : FiniteProbabilityWeights Original)
    (active : Original → FiniteProbabilityWeights Ω)
    (Y : Original → Ω → Out → ℤ)
    (N q : ℕ) [NeZero N] [NeZero q] (hq : q ∣ N)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (gridVolume : ℝ) (hV : gridVolume ≠ 0)
    (center scale : Joint → ℝ) (hscale : ∀ j, 0 < scale j)
    (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D P δ : ℝ} (hD : 0 ≤ D)
    (hP : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P))
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) / scale j ≤ δ) :
    let density := fixedSpatialKernelSliceOriginalForecastDensity B U basis S e rootBudget rootLength z
      lowerG widthG h0 h1 hwG hB lowerP widthP sample
    let Csp : ℝ≥0 := Real.toNNReal ((κ1 * δG ^ Fintype.card X)⁻¹)
    let Ksp : ℝ≥0 := 2 * (Fintype.card X : ℝ≥0) * Csp *
      Real.toNNReal (Fintype.card X * ((Fintype.card X).factorial *
        H ^ (Fintype.card X - 1) / (κ0 * δG ^ Fintype.card X)))
    let C := Csp * allocatedForecastAllAxisLiftCap B hδP
    let L := allocatedForecastAllAxisLiftCap B hδP * Ksp +
      Csp * allocatedForecastAllAxisLiftLip B hδP
    let K := Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R)
    let c := fun a => (sample (selected a).1).2 (selected a).2
    let grid := forecastInactiveFixedOutput B U basis S selected c xref
    let test := W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
      (fun a => (base a : ℝ) / box a) τ
    ‖forecastJointOriginalGridMean U basis S.value hm law active grid Y N q hq
        gridVolume density test center scale -
      (∑' g, 𝔼 r : Out → ZMod N,
        ((rationalInactiveForecast law active grid Y N gridVolume g r / gridVolume : ℝ) : ℂ) *
          ∫ y, test g (fun a => ZMod.castHom hq (ZMod q) (r a)) y
            ∂realDensityMeasure volume density)‖ ≤
      ((cutoff : ℝ) ^ (Fintype.card Out + 1) *
        (2 * 8 ^ Fintype.card Joint * ((L : ℝ) + C * K) * δ) +
        (D / cutoff) * (8 ^ Fintype.card Joint * (L : ℝ) * δ)) *
          6 ^ Fintype.card Cont + 2 * (D / cutoff) := by
  classical
  intro density Csp Ksp C L K c grid test
  have hbnd := fixedSpatialKernelSliceOriginalForecastDensity_bounds_of_det B U basis hR hσ S
    e rootBudget rootLength z lowerG widthG h0 h1 hwG hB lowerP widthP hδP hwP hlP sample hs
    hH hκ0 hκ1 hδG hentry hdet0 hdet1 hmin hmax
  have hdata := fixedSpatialKernelSliceOriginalForecastDensity_probability_data B U basis hR hσ S
    e rootBudget rootLength z lowerG widthG h0 h1 hwG hB lowerP widthP hδP hwP hlP sample hs
  have hsupport : ∀ y, (3 : ℝ) < ‖y‖ → density y = 0 := by
    intro y hy
    exact fixedSpatialKernelSliceOriginalForecastDensity_zero_of_norm_gt_two B U basis hR hσ S
      e rootBudget rootLength z lowerG widthG h0 h1 hwG hB lowerP widthP hδP hwP hlP sample hs
      hwidthP hW hL hsize hz hlG (fun g => hδG.le.trans (hmin g)) hcontainedG y
      (lt_trans (by norm_num) hy)
  have htest := W.forecastShortGridTest_bounds U basis S.value hb o bW R q hm hperiod hcover
    (fun a => (base a : ℝ) / box a) τ
  have h := forecastJointOriginalGridMean_comparison U basis S.value hm law active grid Y N q hq
    gridVolume density test center scale hV cutoff hcutoff hD hP hdecay C L K
    hbnd.2 hdata.1 (fun g r => (htest g r).2)
    (fun y => by rw [abs_of_nonneg (hdata.1 y)]; exact (hbnd.1 y).2)
    (fun g r => (htest g r).1) hscale (radius := 3) (by norm_num) hδ hδ1 hmesh hsupport
  have hmass : (∫ y, density y) = 1 := hdata.2.2
  norm_num only [hmass, mul_one] at h
  exact h

end Erdos3.VectorPolynomial

end

end OAI
