import OAI.Combinatorics.Progressions.Sampling.ForecastActualPhysicalSourceContinuous

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

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
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

local notation "chart" => mixedCoveredJetChart (O := single) U o basis hb bW N
local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chartSource" => forecastDensityPhysicalChartSource B U basis S density selected sample x
  active Y N volume base physicalN τ

local notation "target" => forecastDensityPhysicalTarget B U basis S density selected sample x
  active Y N volume base physicalN τ o hb bW

local notation "deckSource" => forecastDensityPhysicalDeckSource B U basis S density selected sample x
  active Y N volume base physicalN τ

variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ)

theorem forecastDensityPhysicalChartSource_real
    (z : MixedCoveredJetSource I single Eout n N) :
    ((chartSource u z).re : ℂ) = chartSource u z := by
  simp [forecastDensityPhysicalChartSource, forecastDensityPhysicalDeckSource]

theorem forecastDensityPhysicalTarget_real :
    ((target poly hpoly u).re : ℂ) = target poly hpoly u := by
  have hs : chartSource u = fun z => ((chartSource u z).re : ℂ) := by
    funext z
    exact (forecastDensityPhysicalChartSource_real B U basis S density selected sample x
      active Y N volume base physicalN τ u z).symm
  unfold forecastDensityPhysicalTarget
  rw [hs, restrictedComplexChartDensity_real _ _ _
    (mixedCoveredJetChart_injOn U o basis hb bW N _
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j)))]
  simp only [Complex.ofReal_re]

theorem forecastDensityPhysicalTarget_star :
    star (target poly hpoly u) = target poly hpoly u := by
  have h := forecastDensityPhysicalTarget_real B U basis S density selected sample x
    active Y N volume base physicalN τ o hb bW poly hpoly u
  rw [← h]
  simp only [Complex.star_def, Complex.conj_ofReal]

theorem forecastDensityPhysicalTarget_scaled_real (κ : ℝ) :
    (((κ : ℂ) * target poly hpoly u).re : ℂ) = (κ : ℂ) * target poly hpoly u := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.ofReal_mul, forecastDensityPhysicalTarget_real B U basis S density selected sample x
      active Y N volume base physicalN τ o hb bW poly hpoly u]

theorem forecastDensityPhysicalTarget_scaled_star (κ : ℝ) :
    star ((κ : ℂ) * target poly hpoly u) = (κ : ℂ) * target poly hpoly u := by
  have h := forecastDensityPhysicalTarget_scaled_real B U basis S density selected sample x
    active Y N volume base physicalN τ o hb bW poly hpoly u κ
  rw [← h]
  simp only [Complex.star_def, Complex.conj_ofReal]

theorem forecastDensityPhysicalChartSource_nonneg
    (hd : ∀ y, 0 ≤ density y) (hV : 0 ≤ volume)
    (z : MixedCoveredJetSource I single Eout n N) :
    0 ≤ (chartSource u z).re := by
  simp only [forecastDensityPhysicalChartSource, forecastDensityPhysicalDeckSource,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_nonneg (hd _) (rationalInactiveForecast_nonneg _ _ _ _ N hV _ _)

theorem forecastDensityPhysicalTarget_nonneg
    (hd : ∀ y, 0 ≤ density y) (hV : 0 ≤ volume) :
    0 ≤ (target poly hpoly u).re := by
  let p := physicalSingleSiteValue U N poly hpoly (fun i => (u i : ℝ))
  by_cases hp : p ∈ chart '' region
  · obtain ⟨z, hz, he⟩ := hp
    change 0 ≤ (restrictedComplexChartDensity chart region 1 (chartSource u) p).re
    rw [← he, restrictedComplexChartDensity_apply _ _ _ _
      (mixedCoveredJetChart_injOn U o basis hb bW N _
        (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hz,
      Complex.ofReal_one, one_mul]
    exact forecastDensityPhysicalChartSource_nonneg B U basis S density selected sample x
      active Y N volume base physicalN τ u hd hV z
  · change 0 ≤ (restrictedComplexChartDensity chart region 1 (chartSource u) p).re
    rw [restrictedComplexChartDensity_zero _ _ _ _ hp]
    exact le_rfl

theorem forecastDensityPhysicalTarget_scaled_nonneg
    (hd : ∀ y, 0 ≤ density y) (hV : 0 ≤ volume) {κ : ℝ} (hκ : 0 ≤ κ) :
    0 ≤ ((κ : ℂ) * target poly hpoly u).re := by
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg hκ (forecastDensityPhysicalTarget_nonneg B U basis S density selected sample x
    active Y N volume base physicalN τ o hb bW poly hpoly u hd hV)

end Erdos3.VectorPolynomial

end

end OAI
