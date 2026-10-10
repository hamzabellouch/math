import OAI.Combinatorics.Progressions.Polynomial.AllocatedPolynomialUniformModel
import OAI.Combinatorics.Progressions.Polynomial.CoefficientPolynomialIdentity

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
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

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
local notation "Input" => (((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) ×
  ((Σ j, J j) → UnitAddCircle)) × ((Σ j, J j) → UnitAddCircle))

theorem AllocatedModelPhysicalExpansionIdentity.coefficient_sample
    {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
      T → (∀ a, (e a).Term) → Finset (Fin dim) → Input → ℂ)
    (hidentity : AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g)
    (hgrid : ∀ k, 0 < commonSitePeriod e k) (v : X → (Unit ⊕ Fin dim) → ℤ) :
    allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f
        (BooleanCubeKernel.physicalCubeRowSample U d rows p hm v) *
      allocatedFullGridChartModel B U b S rowSets d hb o bW e
        (BooleanCubeKernel.physicalCubeRowSample U d rows p hm v) =
      ∑ label, ∑ i, ∑ k,
        (((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
          allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
            coverSiteCoefficient e k) *
        BooleanCubeKernel.coefficientAmbientModelTerm period (commonSitePeriod e k) (g label i k)
          (coefficientAmbientTorus U (affineCoefficientCoverSample U p hm (period * commonSitePeriod e k)
            (fun k x => (BooleanCubeKernel.standardPhysicalCubeFrame v (k,x) : ℝ)))) := by
  rw [hidentity v]
  apply Finset.sum_congr rfl
  intro label _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  let : NeZero (commonSitePeriod e k) := ⟨(hgrid k).ne'⟩
  rw [BooleanCubeKernel.coefficientAmbientModelTerm_sample U period (commonSitePeriod e k) p hp hm]

theorem allocatedModel_polynomial_identity_coefficient_cover
    (g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) → T → (∀ a, (e a).Term) → Finset (Fin dim) → Input → ℂ)
    (hidentity : ∀ (p : ∀ j, VectorPolynomial (Fin dim) ℝ (J j → ℝ)),
      (∀ j, DegreeLE (1 : Fin dim → ℕ) (j.val + 1) (p j)) →
      ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j),
        AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g)
    (hgrid : ∀ k, 0 < commonSitePeriod e k)
    (D : ℕ) (hD : 0 < D) (hd : d ∣ D)
    (hperiod : ∀ k, period * commonSitePeriod e k ∣ D)
    (z : CoefficientTorus (K := Fin dim) U) :
    let y := euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin dim) (Fin dim) ℤ) rows
      (quotientIntegerCover (coefficientIntegerLattice U) (D / d) z)
    allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
      allocatedFullGridChartModel B U b S rowSets d hb o bW e y =
      ∑ label, ∑ i, ∑ k,
        (((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
          allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
            coverSiteCoefficient e k) *
        BooleanCubeKernel.coefficientAmbientModelTerm period (commonSitePeriod e k) (g label i k)
          ((D / (period * commonSitePeriod e k)) • coefficientAmbientTorus U z) := by
  let coeff := fun t : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) × T × (∀ a, (e a).Term) =>
    (((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
      allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a t.1 t.2.1) *
        coverSiteCoefficient e t.2.2)
  let factors := fun t : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) × T × (∀ a, (e a).Term) =>
    BooleanCubeKernel.coefficientAmbientModelTerm period (commonSitePeriod e t.2.2) (g t.1 t.2.1 t.2.2)
  let M := fun y => allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
    allocatedFullGridChartModel B U b S rowSets d hb o bW e y
  have hid (p : ∀ j, VectorPolynomial (Fin dim) ℝ (J j → ℝ))
      (hp : ∀ j, DegreeLE (1 : Fin dim → ℕ) (j.val + 1) (p j))
      (hm : ∀ j e, coefficients (p j) e ∈ U j)
      (v : Fin dim → (Unit ⊕ Fin dim) → ℤ) :
      M (BooleanCubeKernel.physicalCubeRowSample U d rows p hm v) =
        ∑ t, coeff t * factors t (coefficientAmbientTorus U
          (affineCoefficientCoverSample U p hm (period * commonSitePeriod e t.2.2)
            (fun k x => (BooleanCubeKernel.standardPhysicalCubeFrame v (k,x) : ℝ)))) := by
    rw [show M (BooleanCubeKernel.physicalCubeRowSample U d rows p hm v) = _ from hidentity p hp hm v]
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro label _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    let : NeZero (commonSitePeriod e k) := ⟨(hgrid k).ne'⟩
    exact congrArg (fun t => coeff (label, i, k) * t)
      (BooleanCubeKernel.coefficientAmbientModelTerm_sample U period (commonSitePeriod e k) p hp hm
        (g label i k) v).symm
  have ht := BooleanCubeKernel.coefficient_polynomial_identity_transfer U rows d D hD hd
    (fun t : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) × T × (∀ a, (e a).Term) => period * commonSitePeriod e t.2.2)
    (fun t => hperiod t.2.2) coeff factors M hid z
  simpa only [Fintype.sum_prod_type, coeff, factors, M] using ht

theorem exists_allocated_finite_model_coefficient_cover
    (hdiv : period ∣ d) (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin dim)) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {T : Type*} [Fintype T] (a : T → ℂ)
    (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : ∀ k s, LipschitzWith L (f k s)) (hf1 : ∀ k s z, ‖f k s z‖ ≤ 1)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (Q : ℝ≥0) (hQ : ∀ a, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤ Q)
    :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Llong := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord +
      max (L * Lcoord * period) (4 * period)
    let Lgrid := fun k => max (((Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} * Lg) * Q) *
      Lcoord * commonSitePeriod e k) (4 * commonSitePeriod e k)
    ∃ g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
        T → (∀ a, (e a).Term) → Finset (Fin dim) →
        (((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle)) ×
          ((Σ j, J j) → UnitAddCircle)) → ℂ,
      (∀ label i k s, LipschitzWith (Llong + Lgrid k) (g label i k s)) ∧
      (∀ label i k s z, ‖g label i k s z‖ ≤ 1) ∧
      ∀ (D : ℕ), 0 < D → d ∣ D →
        (∀ k, period * commonSitePeriod e k ∣ D) →
        ∀ z : CoefficientTorus (K := Fin dim) U,
        let y := euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin dim) (Fin dim) ℤ) rows
          (quotientIntegerCover (coefficientIntegerLattice U) (D / d) z)
        allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
          allocatedFullGridChartModel B U b S rowSets d hb o bW e y =
          ∑ label, ∑ i, ∑ k,
            (((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
              allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
                coverSiteCoefficient e k) *
            BooleanCubeKernel.coefficientAmbientModelTerm period (commonSitePeriod e k) (g label i k)
              ((D / (period * commonSitePeriod e k)) • coefficientAmbientTorus U z) := by
  obtain ⟨g, hg, hgb, hid⟩ := exists_allocated_finite_model_polynomial_uniform_expansion
    B U b S x y₀ q d period r hr hb o bW e hdiv hR C hC hchart hbudget
    Cforward hforward K hK a f hf hf1 he Q hQ
  refine ⟨g, hg, hgb, ?_⟩
  intro D hD hd hperiod z
  exact allocatedModel_polynomial_identity_coefficient_cover B U b S x y₀ q d period r hr hb o bW
    e a f g (fun p hp hm => hid p hp hm) (commonSitePeriod_pos e he) D hD hd hperiod z

end Erdos3.VectorPolynomial

end

end OAI
