import OAI.Combinatorics.Progressions.Linear.FixedSpatialKernelNativeHaarJointMean
import OAI.Combinatorics.Progressions.Sampling.ForecastLawPhysicalAmbientHaarComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} {X : Type} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Principal" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
local notation "law" => principalTupleWeights (α := Empty) B degree
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
local notation "lowerSlice" => (fun (a : Active) (_p : B (Subtype.val a) × Fin (degree (Subtype.val a))) => (0 : ℝ))
local notation "widthSlice" => (fun (a : Active) (_p : B (Subtype.val a) × Fin (degree (Subtype.val a))) =>
  ((S.value : ℝ) - 1) / S.value)

variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (xref : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω → Sigma (AllocatedCongruenceRankOutput X Eout
    (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (gridVolume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {pw cw : ℝ} {Lw : ℝ≥0}
variable (Wtest : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable {Tgeo : Type*} [Fintype Tgeo]
variable (e : G ≃ X ⊕ (X ⊕ Tgeo)) (rootBudget rootLength : ℝ) (z : Option G × X → ℝ)
variable (h0 : (fixedSpatialKernelBlock e rootBudget rootLength z false).det ≠ 0)
variable (h1 : (fixedSpatialKernelBlock e rootBudget rootLength z true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
  4 ≤ Fintype.card (B a.val))
local notation "density" => fixedSpatialKernelOriginalForecastDensity B U basis S e rootBudget
  rootLength z h0 h1 hB lowerSlice widthSlice sample
local notation "κ" => ((forecastGeometricJacobian (X := X) (I := I) U basis R S.value gridVolume τ : ℝ) : ℂ)

include hR hσ ν hcompact hlattice in
theorem fixedSpatialNativeAmbientMean_comparison
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hS : 2 ≤ S.value)
    (hσ1 : ∀ a : AllocatedShortIntegerAxis U basis S.value, σ a.val.1 ≤ 1)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (hW : 0 ≤ rootBudget) (hL : 0 ≤ rootLength)
    (hsize : (Fintype.card G : ℝ) * rootLength ≤ rootBudget) (hz : ∀ a, |z a| ≤ 1)
    (hτ : 0 < τ) (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
    (hbase : base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))
    (q : ℕ) [NeZero q] (hq : q ∣ N) (hm : 0 < m)
    (hperiod : Wtest.modulus ∣ q) (hcover : Wtest.cover ∣ q) (hV : 0 < gridVolume)
    {Findex : Type} [Fintype Findex] {pf cf : ℝ} {Lf : ℝ≥0}
    (F : Findex → NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
    (c : Findex → ℂ) (δ : ℝ)
    (happrox : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hmem : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
      ‖κ * forecastDensityPhysicalTarget B U basis S density selected sample xref
        active Y N gridVolume base physicalN τ o hb bW poly hmem u -
        ∑ i, c i * (F i).eval physicalN poly u‖ ≤ δ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (hmem : ∀ j d, coefficients (poly j) d ∈ U j)
    {P E Rrank M : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hX : (Fintype.card X : ℝ) ≤ P) (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ P)
    (hLip : ((Lw * max 1 (Real.toNNReal cf) + Lf * max 1 (Real.toNNReal cw) : ℝ≥0) : ℝ) ≤ Real.exp P)
    (hcoverF : ∀ i, ((Wtest.cover * (F i).cover : ℕ) : ℝ) ≤ Real.exp P)
    (hmodF : ∀ i, ((Wtest.modulus * (F i).modulus : ℕ) : ℝ) ≤ Real.exp P)
    (hmass : ∑ i, ‖c i‖ ≤ M)
    (hlarge : ∀ i, Real.exp ((max P E + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
    (hRrank : Real.exp ((max P E + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
      Rrank (U j) (poly j)) :
    ‖(𝔼 u ∈ integerBox physicalN, Wtest.eval physicalN poly u *
        (κ * forecastDensityPhysicalTarget B U basis S density selected sample xref
          active Y N gridVolume base physicalN τ o hb bW poly hmem u)) -
      forecastJointOriginalGridMean U basis S.value hm law active
        (forecastInactiveFixedOutput B U basis S selected
          (allocatedOriginalSampleInactiveCoefficients B selected sample) xref)
        Y N q hq gridVolume density
        (Wtest.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
          (fun a => (base a : ℝ) / physicalN a) τ)
        (fun j => (forecastJointGridCenter U basis S.value base j : ℝ))
        (forecastJointGridScale U basis R S.value physicalN τ)‖ ≤
      2 * δ + M * Real.exp (-E) := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hSpos : (0 : ℝ) < S.value := by exact_mod_cast S.positive
  have hSreal : (2 : ℝ) ≤ S.value := by exact_mod_cast hS
  have hw : (1 / 2 : ℝ) ≤ ((S.value : ℝ) - 1) / S.value := by
    apply (le_div_iff₀ hSpos).mpr
    linarith
  have hwidth : ∀ a p, |lowerSlice a p| + |widthSlice a p| ≤ 1 := by
    intro a p
    rw [abs_zero, zero_add, abs_of_nonneg (le_trans (by norm_num) hw)]
    apply (div_le_one hSpos).mpr
    linarith
  have hdensity := (fixedSpatialKernelOriginalForecastDensity_bounds B U basis hR hσ S
    e rootBudget rootLength z h0 h1 hB lowerSlice widthSlice hhalf
    (fun _ _ => hw) (fun _ _ => le_rfl) sample hs).2.continuous.measurable
  have hN (i : X) : 0 < physicalN i := by
    exact_mod_cast (Real.exp_pos _).trans_le (hlarge i)
  have hhaar := fixedSpatialKernelNativeHaarMean_eq_jointMean
    (B := B) (U := U) (basis := basis) (S := S) (sample := sample) (x := xref)
    (active := active) (Y := Y) (N := N) (volume := gridVolume) (base := base)
    (physicalN := physicalN) (τ := τ) (o := o) (hb := hb) (bW := bW)
    (Wtest := Wtest) (e := e) (Wgeo := rootBudget) (Lgeo := rootLength) (z := z)
    (h0 := h0) (h1 := h1) (hB := hB) (lower := lowerSlice) (width := widthSlice) (ν := ν)
    hR hσ hs hσ1 r hr hr3 hradius C hC hchart hbudget hhalf
    (fun _ _ => hw) (fun _ _ => le_rfl) hwidth hW hL hsize hz
    hN hτ hmargin hbase q hq hm hperiod hcover hV
  have h := forecastDensityPhysicalTarget_ambientHaarComparison B U basis S density selected sample xref
    active Y N gridVolume base physicalN τ o hb bW ν hdensity Wtest F c κ δ
    (dvd_trans hcover hq) happrox poly hp hmem hP hE hX hdim hLip hcoverF hmodF hmass
    hlarge hRrank hrank
  simp_rw [mul_assoc, integral_const_mul] at h
  rw [← Finset.mul_expect, hhaar] at h
  exact h

end Erdos3.VectorPolynomial

end

end OAI
