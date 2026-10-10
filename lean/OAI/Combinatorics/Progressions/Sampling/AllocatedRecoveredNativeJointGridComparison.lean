import OAI.Combinatorics.Progressions.Sampling.AllocatedFixedPathRecoveredJointGridComparison

namespace OAI

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

local notation "Long" => LayerSamplerLongVariables short G B

local instance recoveredNativeJointModulusNeZero (Pr : Finset ℕ) (A : ℕ → ℕ)
    [∀ p : Pr, NeZero p.val] : NeZero (∏ p : Pr, p.val ^ A p.val) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩

include hR hσ in
theorem allocatedRecoveredNativeJointGridMean_comparison
    (e : G ≃ X ⊕ (X ⊕ T)) (rootBudget rootLength : ℝ) (z : Option G × X → ℝ)
    (h0 : (fixedSpatialKernelBlock e rootBudget rootLength z false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e rootBudget rootLength z true).det ≠ 0)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (hW : 0 ≤ rootBudget) (hL : 0 ≤ rootLength)
    (hsize : (Fintype.card G : ℝ) * rootLength ≤ rootBudget)
    (hz : ∀ a, |z a| ≤ 1)
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hS : 2 ≤ S.value) (hm : 0 < m)
    (τ : ℝ) (base : X → ℤ) (box : X → ℕ)
    (xref : G → IntegerScalarCubeBox Empty S.value)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hnoise : allocatedReadNoise read = noise)
    (hinteger : ∀ j i d, allocatedReadProjection read ⟨j, Sum.inr i⟩ d = (sample j).2 i d)
    {Lrank : ℕ} (spatial : Fin Lrank ↪ G)
    (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis short j, Fin Lrank ↪ B ⟨j,a.val⟩)
    (Dmod : ℕ)
    (hDmod : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ Dmod)
    (Pr : Finset ℕ) [∀ p : Pr, NeZero p.val]
    (Aexp : ℕ → ℕ) (hp : ∀ p ∈ Pr, p.Prime) (Rbad : ℕ)
    (hbad : (∏ p ∈ Pr, p ^ largestTestedBadDepth Aexp
      (allocatedActualPrimeBad short spatial kernel block Pr
        (modularForecastRankConstant m Dmod : ℝ)) p read) ≤ Rbad)
    (origin : ∀ p : Pr, Long → ZMod (p.val ^ Aexp p.val))
    (q : ℕ) [NeZero q] (hq : q ∣ ∏ p : Pr, p.val ^ Aexp p.val)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (gridVolume : ℝ) (hV : gridVolume ≠ 0)
    (center scale : Joint → ℝ) (hscale : ∀ j, 0 < scale j)
    (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) / scale j ≤ δ) :
    let N := ∏ p : Pr, p.val ^ Aexp p.val
    let Cmod := (modularForecastRankConstant m Dmod : ℝ)
    let D := (Rbad : ℝ) ^ (modularRankDecayExponent m Cmod * modularRankChargeFactor m)
    let poly := allocatedForecastPolynomial short base noise (allocatedReadDeck read)
      (allocatedOriginalSampleCongruenceProjection B U basis S sample)
    let pRat := crtPolynomialInputLaw (fun p : Pr => p.val) (fun p : Pr => Aexp p.val)
      (fun _ : Pr => 0)
      (primePower_crt_coprime (fun p : Pr => p.val) (fun p : Pr => Aexp p.val)
        (fun p => hp p.val p.property) Subtype.val_injective) origin
    let active := fun _ : Original => pRat
    let Y := fun v : Original => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let density := fixedSpatialKernelOriginalForecastDensity B U basis S e rootBudget rootLength z
      h0 h1 hB lower width sample
    let C := fixedSpatialOriginalForecastCap B
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength z true h1) (δ := 1 / 2) (by norm_num)
    let L := fixedSpatialOriginalForecastLip B
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength z false h0)
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength z true h1) (δ := 1 / 2) (by norm_num)
    let K := Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R)
    let law := principalTupleWeights (α := Empty) B degree
      (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
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
  intro N Cmod D poly pRat active Y lower width density C L K law c grid test
  have hD : 0 ≤ D := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hP : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ modularRankDecayExponent m Cmod :=
    allocatedCongruenceForecastRankConstant_dimension short hm Dmod hDmod
  have hdecay (v : Original) (χ : AddChar (Out → ZMod N) ℂ) :
      ‖finiteImageCharacteristic (active v) (fun t j => (Y v t j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-modularRankDecayExponent m Cmod) :=
    allocatedRecoveredForecast_crt_decay B U basis S base noise read hnoise sample hinteger
      spatial kernel block hm Pr Aexp hp Cmod (Nat.cast_nonneg _) Rbad hbad origin
      (fun k => (v k.1 k.2 : ℤ)) χ
  exact fixedSpatialNativeJointGridMean_comparison B U basis hR hσ S hb o bW W
    e rootBudget rootLength z h0 h1 hB hW hL hsize hz sample hs hS hm τ base box xref
    active Y N q hq hperiod hcover gridVolume hV center scale hscale cutoff hcutoff
    hD hP hdecay hδ hδ1 hmesh

end Erdos3.VectorPolynomial

end

end OAI
