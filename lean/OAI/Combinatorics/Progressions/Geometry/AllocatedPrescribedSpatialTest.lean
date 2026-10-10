import OAI.Combinatorics.Progressions.Polynomial.AllocatedPolynomialSpatialTest

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [dG : DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (A : ℕ) {p : ℝ}
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α (allocatedComparisonScale (G := G) B U basis hR hσ ((p+2)^(A+3))).value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "P₀" => (p+2)^A
local notation "P" => (p+2)^(A+3)
local notation "S" => allocatedComparisonScale (G := G) B U basis hR hσ P
local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides
local notation "longWeight" => allocatedLongTupleWeights (α := α) B U basis S
local notation "source" => allocatedLongCoefficientSource B U basis hR hσ S
local notation "coefficientScale" => ∏ a, allocatedLongJetOutputScale B U basis S (O := O) a

variable {D N : Type*} [Fintype D] [Fintype N] [DecidableEq N]
variable (c : D → N → ℤ) (index : D → N → PrincipalTupleIndex B (layerSamplerDegree I n))
variable (root : G → ℤ) (selection : α ↪ G)
variable (hP : (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection).det ≠ 0)
variable (M : ℕ) {τ : ℝ} (hτ : 0 < τ)

local notation "H" => allocatedSpatialHeight B U basis S c index selection M τ
local notation "ρ" => smoothJointResolution N (Fintype.card D) selection M (LayerSamplerScale.value S) (m+1) τ
local notation "ξ" => smoothJointWidth N (Fintype.card D) selection M (m+1) τ
local notation "mesh" => smoothJointRadius (Fintype.card D) selection M (m+1) τ
local notation "Q" => (fun (_ : D) (_ : N) => ρ)
local notation "hH" => allocatedSpatialHeight_pos B U basis S c index selection M τ hτ
local notation "hQ" => (fun (_ : D) (_ : N) => And.left (smoothJointParameters_spec D N selection M (LayerSamplerScale.value S) (m+1) hτ))

local notation "spatialScale" => (∏ d, ∏ _i : Unit ⊕ α, H d : ℝ)

theorem allocatedGoodKernel_prescribed_spatial_test (hp : 0 ≤ p)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P₀)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P₀) (hn : ∀ j, (n j : ℝ) ≤ P₀)
    (hM : 0 < M) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    (hτ1 : τ ≤ 1)
    (hMP : (M : ℝ) ≤ Real.exp P₀) (hRP : ∀ j, R j ≤ Real.exp P₀)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P₀) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P₀)
    (hτP : τ⁻¹ ≤ Real.exp P₀)
    (hroot : ∀ j, |root j| ≤ (LayerSamplerScale.value S : ℤ)) :
    (LayerSamplerScale.value S : ℝ) ≤ Real.exp ((p+2)^allocatedComparisonExponent m (A+3)) ∧
    ∃ (modulus : ℕ) (hm : 0 < modulus),
      letI : NeZero modulus := ⟨ne_of_gt hm⟩
      modulus ≤ M^(m+1) ∧
      (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
      (∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
        (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range) ∧
      ∃ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0),
      (∀ j : Fin m, fixedKernelInverseBound (LayerSamplerScale.positive S) x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ))) ∧
      ∃ hsize : ∀ d, (Fintype.card α+1)*modulus ≤ lengths d,
      ∀ u : PrincipalAxisTuples (α := α) grid sides,
      ∃ residue : (PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
          (fun a => layerSamplerDegree I n a.val) → Option α → ZMod modulus) →
          ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus),
        (∀ r y, (allocatedLongResidueWeights B U basis S modulus hm r hsize).weight y ≠ 0 → ∀ j,
          integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j y) modulus = residue r j) ∧
        ∀ (tv : Finset (D → (Unit ⊕ α) → ℤ)),
        (∀ v ∈ tv, ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ)/H d| ≤ 1) →
        ∀ (φ : (D → (Unit ⊕ α) → ℤ) → AllocatedLongJetRows B U basis S O → ℂ),
        (∀ v ∈ tv, Measurable (φ v)) → (∀ v ∈ tv, ∀ z, ‖φ v z‖ ≤ 1) →
        ‖(∫ a, (longWeight).complexMean (fun y => ∑ v ∈ tv,
              ((allocatedSpatialOutputLaw B U basis S u c index x root H Q hH hQ y v).toReal : ℂ)*
                φ v (allocatedLongJetMap B U basis S x u y rows a)) ∂source) -
          ((longWeight).fiberLaw (principalResidueLabel modulus)).complexMean (fun r => ∑ v ∈ tv,
            (allocatedSpatialProxy B U basis S u c index x root selection hP H hH modulus r mesh v /
              (spatialScale : ℂ))*
            (∫ z, ((allocatedLongJetProxy B U basis S x u rows s hA modulus (residue r) z /
                coefficientScale : ℝ) : ℂ)*φ v z ∂allocatedLongJetReference B U basis S O))‖ ≤
          τ := by
  classical
  cases Subsingleton.elim dG (Classical.decEq G)
  have hBudget : P₀ ≤ P := by linarith [polynomialBudget_four_slack A hp]
  have hExp : Real.exp P₀ ≤ Real.exp P := Real.exp_le_exp.mpr hBudget
  obtain ⟨hrho, hlarge, hxi, hxi1, hr⟩ :=
    smoothJointParameters_spec D N selection M (LayerSamplerScale.value S) (m+1) hτ
  have hc := allocatedSpatialHeight_spec B U basis S c index selection M τ hτ
  obtain ⟨hS, modulus, hm, hmod, hspatial, hperiod, s, hA, hi, hsize, hcompare⟩ :=
    allocatedGoodKernel_polynomial_spatial_test B U basis hR hσ (A+3) x rows c index root selection
      hP
      H Q hH hQ hp (hK.trans hBudget) (fun j => (hI j).trans hBudget) (fun j => (hn j).trans hBudget)
      hM hx hq hinj hrows hσ1 (show 0 < τ/4 by positivity) (show τ/4 ≤ 1 by linarith)
      (hMP.trans hExp) (fun j => (hRP j).trans hExp) (fun j => (hRi j).trans hExp)
      (fun j => (hσi j).trans hExp) (quarterAccuracy_polynomial_budget A hp hτP) hroot
      hxi.le hxi1 hc.2.2.2 hrho hc.2.2.1 (fun _ _ => le_rfl) hlarge hr
  refine ⟨hS, modulus, hm, ?_⟩
  let : NeZero modulus := ⟨ne_of_gt hm⟩
  refine ⟨hmod, hspatial, hperiod, s, hA, hi, hsize, ?_⟩
  intro u
  obtain ⟨residue, hmatrix, htest⟩ := hcompare u
  refine ⟨residue, hmatrix, ?_⟩
  intro tv hv φ hφ hb
  have he := htest tv hv φ hφ hb
  have ht := smoothSpatial_grid_tolerance (N := N) selection M (LayerSamplerScale.value S) (m+1)
    hτ hτ1 hmod H (allocatedSpatialHeight_one_le B U basis S c index selection M τ hτ) tv hv
  exact he.trans (by simpa only [smoothVectorSpatialError] using ht.2.2.2.2.2.2)

end Erdos3.VectorPolynomial

end

end OAI
