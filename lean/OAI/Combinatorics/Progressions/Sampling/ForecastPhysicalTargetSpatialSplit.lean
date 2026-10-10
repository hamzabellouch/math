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

noncomputable def forecastDensityPhysicalSplitDeckSource
    (r : X → ZMod N) (v : X → ℝ)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, Eout j → ℤ) : ℂ :=
  (density ((fun a : Spatial => (v a.1 - (base a.1 : ℝ) / physicalN a.1) / (τ / 8)),
    forecastNormalizedActiveCoordinates short (allocatedFullMixedSiteValue (R := R) U basis w)) : ℂ) *
  (rationalInactiveForecast law active
    (forecastInactiveFixedOutput B U basis S selected
      (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
    Y N volume (fun a _ => (w (selected a).1).2 (selected a).2)
    (forecastCongruenceOutput short r
      (fun j i => ((Sum.elim (w j).2 (deck j) i : ℤ) : ZMod N))) : ℂ)

local notation "splitDeckSource" => forecastDensityPhysicalSplitDeckSource B U basis S
  density selected sample x active Y N volume base physicalN τ

noncomputable def forecastDensityPhysicalSplitChartSource
    (r : X → ZMod N) (v : X → ℝ)
    (z : MixedCoveredJetSource I single Eout n N) : ℂ :=
  splitDeckSource r v (fun j => mixedArrayRegroup _ _ _ (z.1 j) ())
    (fun j i => ((z.2 j () i).val : ℤ))

local notation "splitChartSource" => forecastDensityPhysicalSplitChartSource B U basis S
  density selected sample x active Y N volume base physicalN τ

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart (O := single) U o basis hb bW N
local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))

noncomputable def forecastDensityPhysicalSplitTarget
    (r : X → ZMod N) (v : X → ℝ) (y : EuclideanJetLayers U single) : ℂ :=
  restrictedComplexChartDensity chart region 1 (splitChartSource r v) y

local notation "splitTarget" => forecastDensityPhysicalSplitTarget B U basis S
  density selected sample x active Y N volume base physicalN τ o hb bW

theorem forecastDensityPhysicalSplitDeckSource_specialize
    (hphysicalN : ∀ i, 0 < physicalN i) (hτ : 0 < τ) (u : X → ℤ)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, Eout j → ℤ) :
    splitDeckSource (fun i => (u i : ZMod N)) (fun i => (u i : ℝ) / physicalN i) w deck =
      forecastDensityPhysicalDeckSource B U basis S density selected sample x
        active Y N volume base physicalN τ u w deck := by
  have hsp : (fun a : Spatial =>
      ((u a.1 : ℝ) / physicalN a.1 - (base a.1 : ℝ) / physicalN a.1) / (τ / 8)) =
      (fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)) := by
    funext a
    have hN : (physicalN a.1 : ℝ) ≠ 0 := by exact_mod_cast (hphysicalN a.1).ne'
    field_simp [hN, hτ.ne']
  unfold forecastDensityPhysicalSplitDeckSource forecastDensityPhysicalDeckSource
  rw [hsp, forecastCongruenceOutput_intCast]

theorem forecastDensityPhysicalSplitChartSource_specialize
    (hphysicalN : ∀ i, 0 < physicalN i) (hτ : 0 < τ) (u : X → ℤ)
    (z : MixedCoveredJetSource I single Eout n N) :
    splitChartSource (fun i => (u i : ZMod N)) (fun i => (u i : ℝ) / physicalN i) z =
      forecastDensityPhysicalChartSource B U basis S density selected sample x
        active Y N volume base physicalN τ u z := by
  exact forecastDensityPhysicalSplitDeckSource_specialize B U basis S density selected sample x
    active Y N volume base physicalN τ hphysicalN hτ u _ _

theorem forecastDensityPhysicalSplitTarget_specialize
    (hphysicalN : ∀ i, 0 < physicalN i) (hτ : 0 < τ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ) :
    splitTarget (fun i => (u i : ZMod N)) (fun i => (u i : ℝ) / physicalN i)
      (physicalSingleSiteValue U N poly hpoly (fun i => (u i : ℝ))) =
      forecastDensityPhysicalTarget B U basis S density selected sample x
        active Y N volume base physicalN τ o hb bW poly hpoly u := by
  have hs : splitChartSource (fun i => (u i : ZMod N))
      (fun i => (u i : ℝ) / physicalN i) =
      forecastDensityPhysicalChartSource B U basis S density selected sample x
        active Y N volume base physicalN τ u := by
    funext z
    exact forecastDensityPhysicalSplitChartSource_specialize B U basis S density selected sample x
      active Y N volume base physicalN τ hphysicalN hτ u z
  unfold forecastDensityPhysicalSplitTarget forecastDensityPhysicalTarget
  rw [hs]

end Erdos3.VectorPolynomial

end

end OAI
