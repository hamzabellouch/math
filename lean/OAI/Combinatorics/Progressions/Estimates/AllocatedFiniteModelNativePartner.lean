import OAI.Combinatorics.Progressions.Estimates.AllocatedRecenteredIdealError
import OAI.Combinatorics.Progressions.Probability.ExactPhysicalMixtureNativePartner

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin (s + 1)) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin (s + 1))))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "mask" => allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin (s + 1))))

variable {T : Type} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin (s + 1)) → (LayerSamplerAxis I n → ℝ) → ℂ)
local notation "LongSpace" => ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle))
local notation "GridSpace" => ((Σ j, J j) → UnitAddCircle)

variable (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

open BooleanCubeKernel
attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

noncomputable def allocatedFinitePhysicalModelValue (v : Fin nX → (Unit ⊕ Fin (s + 1)) → ℤ) : ℂ :=
  allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f
    (physicalCubeRowSample U d rows p hm v) *
    allocatedFullGridChartModel B U b S rowSets d hb o bW e (physicalCubeRowSample U d rows p hm v)

noncomputable def allocatedFinitePhysicalCubeMean
    (N : Fin nX → ℕ) (input : (Fin nX → ℤ) → ℂ) : ℂ :=
  𝔼 cube : SupportedCube (s + 1) (integerBox N : Set (Fin nX → ℤ)),
    let v := (physicalCubeParametersEquiv (Fin nX) (s + 1)).symm cube.val
    allocatedFinitePhysicalModelValue B U b S x y₀ q d period r hr hb o bW e a f p hm v *
      ∏ site, conjugationPower site.card (input (physicalCubeVertexValue v site))

noncomputable def allocatedFinitePhysicalCoefficient (t : ((Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) × T × (∀ a, (e a).Term))) : ℂ :=
  ((2 : ℂ) ^ Fintype.card (Finset (Fin (s + 1))) *
    allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a t.1 t.2.1) *
      coverSiteCoefficient e t.2.2

variable (g : (Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
  T → (∀ a, (e a).Term) → Finset (Fin (s + 1)) →
  (((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle)) ×
    ((Σ j, J j) → UnitAddCircle)) → ℂ)

noncomputable def allocatedFinitePhysicalTwist (t : ((Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) × T × (∀ a, (e a).Term))) (site : Finset (Fin (s + 1))) (u : Fin nX → ℤ) : ℂ :=
  g t.1 t.2.1 t.2.2 site (physicalMaskedFactorInput period p (fun z => (u z : ℝ)),
    physicalGridFactorInput (commonSitePeriod e t.2.2) p (fun z => (u z : ℝ)))

theorem allocatedFinitePhysicalCoefficient_mass :
    (∑ t, ‖allocatedFinitePhysicalCoefficient (E := E) B U b S x y₀ q d period e a t‖) =
    ∑ label : Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i, ∑ k, ‖((2 : ℂ) ^ Fintype.card (Finset (Fin (s + 1))) *
      allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) * coverSiteCoefficient e k‖ := by
  simp only [allocatedFinitePhysicalCoefficient, Fintype.sum_prod_type]

theorem allocatedFinitePhysicalModelValue_expansion
    (hidentity : AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g)
    (v : Fin nX → (Unit ⊕ Fin (s + 1)) → ℤ) :
    allocatedFinitePhysicalModelValue B U b S x y₀ q d period r hr hb o bW e a f p hm v =
      ∑ t, allocatedFinitePhysicalCoefficient (E := E) B U b S x y₀ q d period e a t * ∏ site,
        allocatedFinitePhysicalTwist B U b S period e p g t site (physicalCubeVertexValue v site) := by
  simp only [Fintype.sum_prod_type]
  exact hidentity v

theorem allocatedFinitePhysicalCubeMean_expansion
    (hidentity : AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g)
    (N : Fin nX → ℕ) (input : (Fin nX → ℤ) → ℂ) :
    allocatedFinitePhysicalCubeMean B U b S x y₀ q d period r hr hb o bW e a f p hm N input =
      ∑ t, allocatedFinitePhysicalCoefficient (E := E) B U b S x y₀ q d period e a t *
        (𝔼 cube : SupportedCube (s + 1) (integerBox N : Set (Fin nX → ℤ)),
          let v := (physicalCubeParametersEquiv (Fin nX) (s + 1)).symm cube.val
          ∏ site, conjugationPower site.card (input (physicalCubeVertexValue v site)) *
            allocatedFinitePhysicalTwist B U b S period e p g t site (physicalCubeVertexValue v site)) := by
  unfold allocatedFinitePhysicalCubeMean
  simp_rw [allocatedFinitePhysicalModelValue_expansion B U b S x y₀ q d period r hr hb o bW e a f p hm g hidentity]
  simp only [Finset.sum_mul, mul_assoc, Finset.expect_sum_comm, ← Finset.mul_expect]
  apply Finset.sum_congr rfl
  intro t ht
  congr 1
  apply Finset.expect_congr rfl
  intro cube hcube
  rw [Finset.prod_mul_distrib]
  ring

theorem allocatedFiniteModelPhysical_native_partner
    (hg : ∀ label i k site z, ‖g label i k site z‖ ≤ 1)
    (hidentity : AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g)
    (N : Fin nX → ℕ) [∀ z, NeZero (N z)]
    (input : (Fin nX → ℤ) → ℂ) (hinput : ∀ u ∈ integerBox N, ‖input u‖ ≤ 1)
    {budget : ℝ} (hbudget : 0 ≤ budget) (hdimension : (nX : ℝ) ≤ budget)
    (hmass : (∑ t, ‖allocatedFinitePhysicalCoefficient (E := E) B U b S x y₀ q d period e a t‖) ≤ Real.exp budget)
    (hpositive : Real.exp (-budget) ≤
      (allocatedFinitePhysicalCubeMean B U b S x y₀ q d period r hr hb o bW e a f p hm N input).re) :
    ∃ (t : ((Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) × T × (∀ a, (e a).Term))) (V : NativeSampleCorrelation (fun _ : Fin nX => 1) s
        ((budget + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))
        (integerBox N) id (fun u => input u * allocatedFinitePhysicalTwist B U b S period e p g t ∅ u)),
      V.test.normBound ≤ 1 := by
  apply native_partner_of_exact_physical_mixture N input
    (allocatedFinitePhysicalCoefficient (E := E) B U b S x y₀ q d period e a)
    (allocatedFinitePhysicalTwist B U b S period e p g) hbudget hdimension hinput
    (fun t site u => hg _ _ _ _ _) hmass hpositive
  exact allocatedFinitePhysicalCubeMean_expansion B U b S x y₀ q d period r hr hb o bW e a f p hm g hidentity N input

end Erdos3.VectorPolynomial

end

end OAI
