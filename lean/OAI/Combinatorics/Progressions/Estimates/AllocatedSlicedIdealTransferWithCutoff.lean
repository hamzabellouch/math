import OAI.Combinatorics.Progressions.Lattices.AllocatedResidueCoefficientL1WithCutoff
import OAI.Combinatorics.Progressions.Probability.DensityComparisonComposition

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)
variable (d : ℕ) (hcutoff : AllocatedTailCutoffCompatible U basis S.value d)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => layerSamplerDegree I n (Subtype.val a))
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides
local notation "tupleIndex" => PrincipalTupleIndex activeB activeDegree
local notation "positiveLengths" => (fun j : tupleIndex => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

include hcutoff

theorem allocatedSlicedLongJet_coefficient_l1_withCutoff {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ d+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P e ε : ℝ} (hP : 0 ≤ P) (he : 0 ≤ e) (hε : 0 < ε)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hεe : ε⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLogWithCutoff (G := G) B d α O P e) ≤ S.value)
    (modulus : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range)
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
    (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ)))
    (u : PrincipalAxisTuples (α := α) grid sides)
    (H step : tupleIndex → ℕ) (c : tupleIndex → ℤ) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (lengths j : ℤ))
    (hm : 0 < modulus) (r : tupleIndex → Option α → ZMod modulus)
    (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree lengths H step c positiveLengths hH
      hsubset modulus hm r hsize).weight v₀ ≠ 0) :
    let C := Real.exp (allocatedDensityLog (G := G) B α O P)
    let CM : ℝ := layerKernelIndexBound (max m d) M
    let T := Real.exp (allocatedJetSupportLog (G := G) B α O P)
    let law := containedProgressionResidueLaw activeB activeDegree lengths H step c positiveLengths hH
      hsubset modulus hm r hsize
    let residue := fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
    let proxy := fun z => (principalResidueWeights activeB activeDegree H hH modulus hm r hsize).mean
      (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
        (principalTupleFlatten activeB activeDegree α
          (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / lengths j)) z)
    Integrable (allocatedLongProfileDensity B U basis S x rows modulus residue proxy)
      (allocatedLongJetReference B U basis S O) ∧
    (∫ z, |law.mean (fun v => allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z) -
        allocatedLongProfileDensity B U basis S x rows modulus residue proxy z|
      ∂allocatedLongJetReference B U basis S O) ≤
      (2*T+1)^Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
        (Fintype.card {a // ¬grid a} * ε * (1 + CM * C + ε)^Fintype.card {a // ¬grid a}) := by
  intro C CM T law residue proxy
  have hr (v) (hv : law.weight v ≠ 0) (j : Fin m) :
      integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v) modulus = residue j := by
    exact containedProgressionResidueLaw_matrix activeB activeDegree lengths H step c positiveLengths hH
      hsubset modulus hm r hsize (allocatedNonkernelExponent B j)
      (partitionedPrincipalInput grid (fun g a => (g,a)))
      (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u))
      (rows j) v v₀ hv hv₀
  have he := allocatedLongJet_residue_coefficient_l1_withCutoff B U basis hR hσ S x rows d hcutoff
    hM selection hx hq hinj hrows hσ1 hP he hε hMP hRP hRi hσi hcount hεe hlarge
    modulus hperiod s hA hi u law residue hr
  have hp : (fun z => law.mean (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
      (principalTupleNormalized lengths v) z)) = proxy := by
    funext z
    exact containedProgressionResidueLaw_mean activeB activeDegree lengths H step c positiveLengths hH
      hsubset modulus hm r hsize (fun y => allocatedNormalizedLongJetDensity B U basis S x u rows s hA y z)
  dsimp only at he
  rw [hp] at he
  exact he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)
variable (d : ℕ) (hcutoff : AllocatedTailCutoffCompatible U basis S.value d)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => layerSamplerDegree I n (Subtype.val a))
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides
local notation "tupleIndex" => PrincipalTupleIndex activeB activeDegree
local notation "positiveLengths" => (fun j : tupleIndex => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

include hcutoff

theorem allocatedSlicedLongJet_ideal_transfer_withCutoff {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ d+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P e ε : ℝ} (hP : 0 ≤ P) (he : 0 ≤ e) (hε : 0 < ε)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hεe : ε⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLogWithCutoff (G := G) B d α O P e) ≤ S.value)
    (modulus : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range)
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
    (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ)))
    (u : PrincipalAxisTuples (α := α) grid sides)
    (H step : tupleIndex → ℕ) (c : tupleIndex → ℤ) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (lengths j : ℤ))
    (hm : 0 < modulus) (r : tupleIndex → Option α → ZMod modulus)
    (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree lengths H step c positiveLengths hH
      hsubset modulus hm r hsize).weight v₀ ≠ 0)
    (g : AllocatedLongJetRows B U basis S O → ℝ)
    (hg : Integrable g (allocatedLongJetReference B U basis S O)) {Eref : ℝ} :
    let C := Real.exp (allocatedDensityLog (G := G) B α O P)
    let CM : ℝ := layerKernelIndexBound (max m d) M
    let T := Real.exp (allocatedJetSupportLog (G := G) B α O P)
    let law := containedProgressionResidueLaw activeB activeDegree lengths H step c positiveLengths hH
      hsubset modulus hm r hsize
    let residue := fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
    let proxy := fun z => (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α
      (H j) modulus (hH j) (fun _ => modulus) (r j) (fun _ => hm) (fun _ => le_rfl) (hsize j))).mean
      (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
        (principalTupleFlatten activeB activeDegree α
          (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / lengths j)) z)
    (∫ z, |g z - allocatedLongProfileDensity B U basis S x rows modulus residue proxy z|
      ∂allocatedLongJetReference B U basis S O) ≤ Eref →
    (∫ z, |law.mean (fun v => allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z) - g z|
      ∂allocatedLongJetReference B U basis S O) ≤
      (2*T+1)^Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
        (Fintype.card {a // ¬grid a} * ε * (1 + CM * C + ε)^Fintype.card {a // ¬grid a}) + Eref := by
  intro C CM T law residue proxy href
  have hcoef := allocatedSlicedLongJet_coefficient_l1_withCutoff B U basis hR hσ S x rows d hcutoff
    hM selection hx hq hinj hrows hσ1 hP he hε hMP hRP hRi hσi hcount hεe hlarge
    modulus hperiod s hA hi u H step c hH hsubset hm r hsize v₀ hv₀
  have hfi : Integrable (fun z => law.mean
      (fun v => allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z))
      (allocatedLongJetReference B U basis S O) :=
    law.mean_integrable _ _ (fun v =>
      (allocatedLongJetDensity_probability_data B U basis hR hσ S x u v rows s hA hσ1).2.1)
  exact density_l1_triangle_bound_reverse (allocatedLongJetReference B U basis S O)
    _ _ _ hfi hcoef.1 hg hcoef.2 href

end Erdos3.VectorPolynomial

end

end OAI
