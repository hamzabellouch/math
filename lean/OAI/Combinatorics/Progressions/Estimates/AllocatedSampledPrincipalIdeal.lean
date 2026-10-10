import OAI.Combinatorics.Progressions.Probability.SampledWeightedMixtureError

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable (hR : ∀ j, 0 < R j)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (q : ℕ) (δ : ℝ≥0)

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "amp" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖
local notation "principalTuples" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
  (allocatedPrincipalSides B U b S)
local notation "actual" => (fun t => allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q t
  (allocatedPhysicalLongIdeal B U b hR S rowSets δ))

theorem allocatedProductIdealError_principal_sampled
    {X : Type*} [Fintype X]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (stride : X → ℕ) (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride))
    (V : Option (Fin dim) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    (law : FiniteProbabilityWeights principalTuples)
    (P : principalTuples → EuclideanJetLayers U rowTypes → ℂ)
    (W : (Option (Fin dim) × X → ℤ) → principalTuples → ℂ)
    (hW : ∀ z t, ‖W z t‖ ≤ 1)
    {A ε M : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (herr : ∀ t y, ‖actual t y - P t y‖ ≤ amp * A * (‖cutoff y‖ * ε))
    (hcutoff : selectedResidueDensityMass stride cells V
      (fun z => amp * ‖cutoff (physicalCubeRowSample U d rows p hm (standardPhysicalCubeOutput z))‖) ≤ M) :
    let sample := fun z => physicalCubeRowSample U d rows p hm (standardPhysicalCubeOutput z)
    let error := fun z => law.complexMean (fun t => W z t * (actual t (sample z) - P t (sample z)))
    selectedResidueDensityMass stride cells V (fun z => ‖error z‖) ≤ (A * ε) * M ∧
    ∀ φ : (Option (Fin dim) × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
      ‖∑' z, ((selectedResidueSmoothPMF stride cells V hV hZ z).toReal : ℂ) *
        (error z * φ z)‖ ≤ (A * ε) * M := by
  intro sample error
  have hpoint (z : Option (Fin dim) × X → ℤ) (t : principalTuples) :
      ‖actual t (sample z) - P t (sample z)‖ ≤ (A * ε) * (amp * ‖cutoff (sample z)‖) := by
    apply (herr t (sample z)).trans_eq
    ring
  have h := selectedResidue_weightedMixture_error law (fun _ => A * ε)
    (fun _ => mul_nonneg hA hε) stride cells V hV hZ
    (fun z t => actual t (sample z) - P t (sample z)) W
    (fun z => amp * ‖cutoff (sample z)‖) hpoint hW hcutoff
  simpa only [FiniteProbabilityWeights.mean_const] using h

end Erdos3.BooleanCubeKernel

end

end OAI
