import OAI.Combinatorics.Progressions.Estimates.AllocatedComparisonScale
import OAI.Combinatorics.Progressions.Probability.AllocatedSpatialMixture

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (A : ℕ) {p : ℝ}
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α (allocatedComparisonScale (G := G) B U basis hR hσ ((p+2)^A)).value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "P" => (p+2)^A
local notation "S" => allocatedComparisonScale (G := G) B U basis hR hσ P
local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides
local notation "scale" => ∏ a, allocatedLongJetOutputScale B U basis S (O := O) a

theorem allocatedGoodKernel_polynomial_test (hp : 0 ≤ p)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    {M : ℕ} (hM : 0 < M) (selection : α ↪ G)
    (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hηP : η⁻¹ ≤ Real.exp P) :
    (LayerSamplerScale.value S : ℝ) ≤ Real.exp ((p+2)^allocatedComparisonExponent m A) ∧
    ∃ (modulus : ℕ) (hm : 0 < modulus), modulus ≤ M^(m+1) ∧
      (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
      (∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
        (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range) ∧
      ∃ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0),
      (∀ j : Fin m, fixedKernelInverseBound (LayerSamplerScale.positive S) x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ))) ∧
      ∃ hsize : ∀ d, (Fintype.card α+1)*modulus ≤ lengths d,
      ∀ (u : PrincipalAxisTuples (α := α) grid sides)
        (r : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
          (fun a => layerSamplerDegree I n a.val) → Option α → ZMod modulus),
      let w := allocatedLongResidueWeights B U basis S modulus hm r hsize
      ∃ residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus),
        (∀ v, w.weight v ≠ 0 → ∀ j,
          integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v) modulus = residue j) ∧
        ∀ (φ : AllocatedLongJetRows B U basis S O → ℂ), Measurable φ → (∀ z, ‖φ z‖ ≤ 1) →
        ‖(∫ c, w.complexMean (fun v => φ (allocatedLongJetMap B U basis S x u v rows c))
            ∂allocatedLongCoefficientSource B U basis hR hσ S) -
          ∫ z, ((allocatedLongJetProxy B U basis S x u rows s hA modulus residue z/scale : ℝ) : ℂ)*φ z
            ∂allocatedLongJetReference B U basis S O‖ ≤ η := by
  have hP : 0 ≤ P := by positivity
  have hd := allocatedComparisonDimensions_of_primitive B rows hq hinj hP hK hI hn
  have hpD := (allocatedComparisonDimension_bounds m hP).2.2.1
  have hexp := Real.exp_le_exp.mpr hpD
  have hcount (j : Fin m) :
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤
        Real.exp (allocatedComparisonDimension m P) :=
    (add_le_add (hd.coefficients j) (le_refl (1 : ℝ))).trans (Real.add_one_le_exp _)
  refine ⟨allocatedComparisonScale_polynomial_upper (G := G) B U basis hR hσ A hp hK hn hRi hσi, ?_⟩
  exact allocatedGoodKernel_prescribed_test B U basis hR hσ S x rows hM selection hx hq hinj hrows hσ1
    hd.nonneg hd.nonneg hη hη1 (hMP.trans hexp) (fun j => (hRP j).trans hexp)
    (fun j => (hRi j).trans hexp) (fun j => (hσi j).trans hexp) hcount (hηP.trans hexp)
    (allocatedComparisonScale_ready (G := G) B U basis hR hσ rows hq hinj hP hK hI hn)

end Erdos3.VectorPolynomial

end

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
variable (x : G → IntegerScalarCubeBox α (allocatedComparisonScale (G := G) B U basis hR hσ ((p+2)^A)).value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "P" => (p+2)^A
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
variable (H : D → ℝ) (Q : D → N → ℝ) (hH : ∀ d, 0 < H d) (hQ : ∀ d j, 0 < Q d j)

local notation "spatialScale" => (∏ d, ∏ _i : Unit ⊕ α, H d : ℝ)

theorem allocatedGoodKernel_polynomial_spatial_test (hp : 0 ≤ p)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    {M : ℕ} (hM : 0 < M) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hηP : η⁻¹ ≤ Real.exp P)
    (hroot : ∀ j, |root j| ≤ (LayerSamplerScale.value S : ℤ))
    {ρ ξ mesh : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hwidth : ∀ d j, ((|c d j| : ℤ)+(sides (index d j) : ℤ) : ℝ)*Q d j ≤ ξ*H d)
    (hρ : 0 < ρ) (hscale : ∀ d, ρ ≤ H d/LayerSamplerScale.value S) (hscaleQ : ∀ d j, ρ ≤ Q d j)
    (hlarge : smoothSpatialMeshThreshold α G N (LayerSamplerScale.value S) ≤ ρ) (hmesh : 0 < mesh) :
    (LayerSamplerScale.value S : ℝ) ≤ Real.exp ((p+2)^allocatedComparisonExponent m A) ∧
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
        let Δ := smoothVectorSpatialError D N selection M (LayerSamplerScale.value S) modulus ρ ξ mesh /
          spatialScale*tv.card
        ‖(∫ a, (longWeight).complexMean (fun y => ∑ v ∈ tv,
              ((allocatedSpatialOutputLaw B U basis S u c index x root H Q hH hQ y v).toReal : ℂ)*
                φ v (allocatedLongJetMap B U basis S x u y rows a)) ∂source) -
          ((longWeight).fiberLaw (principalResidueLabel modulus)).complexMean (fun r => ∑ v ∈ tv,
            (allocatedSpatialProxy B U basis S u c index x root selection hP H hH modulus r mesh v /
              (spatialScale : ℂ))*
            (∫ z, ((allocatedLongJetProxy B U basis S x u rows s hA modulus (residue r) z /
                coefficientScale : ℝ) : ℂ)*φ v z ∂allocatedLongJetReference B U basis S O))‖ ≤
          Δ+(1+Δ)*η := by
  classical
  cases Subsingleton.elim dG (Classical.decEq G)
  obtain ⟨hS, modulus, hm, hmod, hspatial, hperiod, s, hA, hi, hsize, hcompare⟩ :=
    allocatedGoodKernel_polynomial_test B U basis hR hσ A x rows hp hK hI hn hM selection hx
      hq hinj hrows hσ1 hη hη1 hMP hRP hRi hσi hηP
  refine ⟨hS, modulus, hm, ?_⟩
  let : NeZero modulus := ⟨ne_of_gt hm⟩
  refine ⟨hmod, hspatial, hperiod, s, hA, hi, hsize, ?_⟩
  intro u
  have hc := hcompare u
  dsimp only at hc
  choose residue hmatrix htest using hc
  refine ⟨residue, hmatrix, ?_⟩
  intro tv hv φ hφ hb
  exact allocatedSpatial_integral_comparison B U basis hR hσ S u c index x root selection hP H Q hH hQ rows
    hM hx hroot modulus hm (hspatial root) hsize hξ0 hξ1 hwidth hρ hscale hscaleQ hlarge hmesh hη.le
    tv hv (fun r v => ∫ z,
      ((allocatedLongJetProxy B U basis S x u rows s hA modulus (residue r) z /
        coefficientScale : ℝ) : ℂ)*φ v z ∂allocatedLongJetReference B U basis S O)
    φ hφ hb (fun r v hvt => htest r (φ v) (hφ v hvt) (hb v hvt))

end Erdos3.VectorPolynomial

end

end OAI
