import OAI.Combinatorics.Progressions.Lattices.AllocatedNormalizedProductResidueCover
import OAI.Combinatorics.Progressions.Probability.SampledWeightedMixtureError

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (q : ℕ) [NeZero q]
variable (W : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S q r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "labelType" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q)
local notation "positiveLabels" => AllocatedPositiveResidue (dim := dim) B U b S q
local notation "law" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
local notation "residueLaw" => FiniteProbabilityWeights.fiberLaw (law) (principalResidueLabel q)
local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "positiveRadius" => allocatedProductIdealSiteRadius_pos (G := G) B rowSets
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d radius positiveRadius
local notation "amp" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖

variable (g : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
  (∀ a, ((W r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ))
variable (P : AllocatedPositiveResidue (dim := dim) B U b S q →
  EuclideanJetLayers U (fun j : Fin m =>
    {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) (j.val + 1)}) → ℂ)

noncomputable def allocatedFullGridIdealReplacement {X : Type*}
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j a, coefficients (p j) a ∈ U j) (v : X → (Unit ⊕ Fin dim) → ℤ)
    (r : labelType) : ℂ :=
  if hr : 0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r)) then
    let rr : positiveLabels := ⟨r, hr⟩
    P rr (physicalCubeRowSample U d rows p hm v) *
      ∑ k, coverSiteCoefficient (W rr).expansion k * ∏ s,
        g rr k s (fun a => (((eval (fun z => (physicalCubeVertexValue v s z : ℝ))
          (p a.1) a.2) / commonSitePeriod (W rr).expansion k : ℝ) : UnitAddCircle))
  else 0

variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
local notation "actual" => (fun r : positiveLabels => allocatedProductFullGridPrefactor B U b S rowSets
  d radius positiveRadius x hb o bW q (AllocatedFullGridResidueWitness.representative (W r)) (allocatedPhysicalLongIdeal B U b hR S rowSets δ))

omit [NeZero q] in
theorem allocatedProductFullGridCoverValue_ideal_error
    {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hg : ∀ r k s u, ‖g r k s u‖ ≤ 1)
    (herr : ∀ r y, ‖actual r y - P r y‖ ≤ amp * A * (‖cutoff y‖ * ε))
    {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j a, coefficients (p j) a ∈ U j) (v : X → (Unit ⊕ Fin dim) → ℤ)
    (r : labelType) :
    let e : labelType → ℝ := fun r =>
      if hr : 0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r)) then
        ∑ k, ‖coverSiteCoefficient (W ⟨r, hr⟩).expansion k‖ else 0
    ‖allocatedProductFullGridCoverValue B U b hR S q W hb o bW d g δ x p hm v r -
      allocatedFullGridIdealReplacement B U b S q W d g P p hm v r‖ ≤
      e r * ((A * ε) * (amp * ‖cutoff (physicalCubeRowSample U d rows p hm v)‖)) := by
  intro e
  by_cases hr : 0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))
  · let rr : positiveLabels := ⟨r, hr⟩
    let gridValue := ∑ k, coverSiteCoefficient (W rr).expansion k * ∏ s,
      g rr k s (fun a => (((eval (fun z => (physicalCubeVertexValue v s z : ℝ))
        (p a.1) a.2) / commonSitePeriod (W rr).expansion k : ℝ) : UnitAddCircle))
    have hsum : ‖gridValue‖ ≤ ∑ k, ‖coverSiteCoefficient (W rr).expansion k‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      have hp : ‖∏ s, g rr k s (fun a => (((eval (fun z => (physicalCubeVertexValue v s z : ℝ))
          (p a.1) a.2) / commonSitePeriod (W rr).expansion k : ℝ) : UnitAddCircle))‖ ≤ 1 := by
        rw [norm_prod]
        exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun s _ => hg rr k s _)
      exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (mul_one _)
    have he : ‖actual rr (physicalCubeRowSample U d rows p hm v) -
        P rr (physicalCubeRowSample U d rows p hm v)‖ ≤
        (A * ε) * (amp * ‖cutoff (physicalCubeRowSample U d rows p hm v)‖) := by
      apply (herr rr _).trans_eq
      ring
    simp only [allocatedProductFullGridCoverValue, allocatedFullGridIdealReplacement, e, dite_eq_left hr]
    change ‖actual rr (physicalCubeRowSample U d rows p hm v) * gridValue -
      P rr (physicalCubeRowSample U d rows p hm v) * gridValue‖ ≤ _
    rw [← sub_mul, norm_mul]
    exact (mul_le_mul he hsum (norm_nonneg _)
      (mul_nonneg (mul_nonneg hA hε) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))).trans_eq (mul_comm _ _)
  · simp only [allocatedProductFullGridCoverValue, allocatedFullGridIdealReplacement, e,
      dite_eq_right hr, sub_self, norm_zero, zero_mul, le_refl]

theorem allocatedProductFullGridCoverValue_ideal_sampled
    {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hg : ∀ r k s u, ‖g r k s u‖ ≤ 1)
    (herr : ∀ r y, ‖actual r y - P r y‖ ≤ amp * A * (‖cutoff y‖ * ε))
    {X : Type*} [Fintype X]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j a, coefficients (p j) a ∈ U j)
    (stride : X → ℕ) (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride))
    (V : Option (Fin dim) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    (weight : (Option (Fin dim) × X → ℤ) → labelType → ℂ) (hweight : ∀ z r, ‖weight z r‖ ≤ 1)
    {T : ℝ} (hcutoff : selectedResidueDensityMass stride cells V
      (fun z => amp * ‖cutoff (physicalCubeRowSample U d rows p hm (standardPhysicalCubeOutput z))‖) ≤ T) :
    let source := fun z r => allocatedProductFullGridCoverValue B U b hR S q W hb o bW d g δ x p hm
      (standardPhysicalCubeOutput z) r
    let target := fun z r => allocatedFullGridIdealReplacement B U b S q W d g P p hm
      (standardPhysicalCubeOutput z) r
    let error := fun z => (residueLaw).complexMean (fun r => weight z r * source z r) -
      (residueLaw).complexMean (fun r => weight z r * target z r)
    selectedResidueDensityMass stride cells V (fun z => ‖error z‖) ≤
      (allocatedClippedFullGridCoverCoefficientMass B U b S q W * (A * ε)) * T ∧
    ∀ φ : (Option (Fin dim) × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
      ‖∑' z, ((selectedResidueSmoothPMF stride cells V hV hZ z).toReal : ℂ) * (error z * φ z)‖ ≤
        (allocatedClippedFullGridCoverCoefficientMass B U b S q W * (A * ε)) * T := by
  intro source target error
  let e : labelType → ℝ := fun r =>
    if hr : 0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r)) then
      ∑ k, ‖coverSiteCoefficient (W ⟨r, hr⟩).expansion k‖ else 0
  have he (r : labelType) : 0 ≤ e r := by
    dsimp only [e]
    split_ifs
    · exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    · exact le_rfl
  have hpoint (z : Option (Fin dim) × X → ℤ) (r : labelType) :
      ‖source z r - target z r‖ ≤ (e r * (A * ε)) *
        (amp * ‖cutoff (physicalCubeRowSample U d rows p hm (standardPhysicalCubeOutput z))‖) :=
    (allocatedProductFullGridCoverValue_ideal_error B U b hR S q W hb o bW d g P δ x
      hA hε hg herr p hm (standardPhysicalCubeOutput z) r).trans_eq (mul_assoc _ _ _).symm
  have hmean : (residueLaw).mean (fun r => e r * (A * ε)) =
      allocatedClippedFullGridCoverCoefficientMass B U b S q W * (A * ε) := by
    calc
      _ = (residueLaw).mean (fun r => (A * ε) * e r) :=
        congrArg (residueLaw).mean (funext (fun r => mul_comm _ _))
      _ = (A * ε) * (residueLaw).mean e := (residueLaw).mean_const_mul _ _
      _ = _ := mul_comm _ _
  have herror : error = fun z => (residueLaw).complexMean (fun r => weight z r * (source z r - target z r)) := by
    funext z
    dsimp only [error]
    rw [← FiniteProbabilityWeights.complexMean_sub]
    exact congrArg (residueLaw).complexMean (funext (fun r => (mul_sub _ _ _).symm))
  rw [herror]
  have h := selectedResidue_weightedMixture_error (residueLaw) (fun r => e r * (A * ε))
    (fun r => mul_nonneg (he r) (mul_nonneg hA hε)) stride cells V hV hZ
    (fun z r => source z r - target z r) weight
    (fun z => amp * ‖cutoff (physicalCubeRowSample U d rows p hm (standardPhysicalCubeOutput z))‖)
    hpoint hweight hcutoff
  simpa only [hmean] using h

end Erdos3.VectorPolynomial

end

end OAI
