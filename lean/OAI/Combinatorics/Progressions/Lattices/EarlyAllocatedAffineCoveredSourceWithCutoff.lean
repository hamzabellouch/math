import OAI.Combinatorics.Progressions.Estimates.AllocatedSlicedIdealTransferWithCutoff
import OAI.Combinatorics.Progressions.Lattices.AllocatedAffineWholeProfileComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uJ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)
variable (d : ℕ)

include hrows hcard in
theorem allocatedAffineCoefficient_from_reference_l1_withCutoff
    {δ η : ℝ} (hδ : 0 < δ) (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0)
    (hρpos : ∀ P, 0 < ρ P) (hρone : ∀ P, ρ P ≤ 1) (t : ℝ) (htone : t ≤ 1) :
  ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
        (S : LayerSamplerScale (G := G) B U basis R σ)
        (_hcutoff : AllocatedTailCutoffCompatible U basis S.value d),
      ∀ (hσsmall : ∀ j, σ j ≤ t),
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)),
      ∀ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      ∀ {Mk : ℕ} (_hMk : 0 < Mk)
        (_hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j)
          (s j) (hA j) (1 / (Mk : ℝ)))
        {P : ℝ} (_hP : 0 ≤ P) (_hMkP : (Mk : ℝ) ≤ Real.exp P)
        (_hRP : ∀ j, R j ≤ Real.exp P) (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (_hcount : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P),
      let L := principalAxisLength (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a) (allocatedPrincipalSides B U basis S)
      let hL := fun j : PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) => allocatedPrincipalSides_pos B U basis S
        (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j))
      ∀ (H step : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℕ) (c : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℤ)
        (_hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
        (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
        (_hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
        (modulus : ℕ) (hm : 0 < modulus)
        (residue : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → Option α → ZMod modulus)
        (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)
        (_hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H j) < volume.real (scalarCubeDomain α))
        {ε : ℝ} (_hε : 0 ≤ ε) (_hmesh : ∀ j, (step j : ℝ) / L j ≤ ε)
        (selection : α ↪ G) (_hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
        (_hq : Fintype.card α ≤ d + 1)
        {e εcoef : ℝ} (_he : 0 ≤ e) (_hεcoef : 0 < εcoef) (_hεe : εcoef⁻¹ ≤ Real.exp e)
        (_hlarge : Real.exp (allocatedKernelReplacementLogWithCutoff (G := G) B d α O P e) ≤ S.value)
        (_hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
        (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a) (allocatedPrincipalSides B U basis S))
        (_hv₀ : (containedProgressionResidueLaw (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step c hL
          (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0),
      let outputResidue := fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
      ∀ {mesh Cmask : ℝ} (_hmesh0 : 0 ≤ mesh) (_hmesh1 : mesh ≤ 1)
        (_hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
        (_hCmask : 1 ≤ Cmask)
        (_hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (outputResidue j) z ∧
          allocatedIntegerKernelMask B U basis S x rows j modulus (outputResidue j) z ≤ Cmask),
      let center := principalProgressionSliceCenter (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L c
      let width := principalProgressionSliceWidth (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step
      let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) => R o.1.val.1)
        (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width)
      let law := containedProgressionResidueLaw (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step c hL
        (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset modulus hm residue hsize
      let proxy := fun z : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) → ℝ =>
        (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (H j) modulus
          (lt_of_lt_of_le (by decide : 0 < 2) (hH j)) (fun _ => modulus) (residue j) (fun _ => hm) (fun _ => le_rfl) (hsize j))).mean
          (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
            (principalTupleFlatten (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) α
              (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j)) z)
      (∫ z, |allocatedLongProfileDensity B U basis S x rows modulus outputResidue ideal z -
        allocatedLongProfileDensity B U basis S x rows modulus outputResidue proxy z|
        ∂allocatedLongJetReference B U basis S O) ≤
        allocatedAffineSourceReferenceError B U basis S α O
          (ρ (allocatedGridAxis (I := I) U basis S.value)) P η (fun _ => modulus) H ε mesh Cmask →
      (∫ z, |law.mean (fun v => allocatedLongJetDensity B U basis hR hσ S x u v rows s hA
            (fun j => (hσsmall j).trans htone) z) -
          allocatedLongProfileDensity B U basis S x rows modulus outputResidue ideal z|
        ∂allocatedLongJetReference B U basis S O) ≤
        (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P) + 1)^
          Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
          (Fintype.card {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} * εcoef *
            (1 + (layerKernelIndexBound (max m d) Mk : ℝ) * Real.exp (allocatedDensityLog (G := G) B α O P) + εcoef)^
              Fintype.card {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}) +
        allocatedAffineSourceReferenceError B U basis S α O
          (ρ (allocatedGridAxis (I := I) U basis S.value)) P η (fun _ => modulus) H ε mesh Cmask
 := by
  intro J _ U basis R σ hR hσ S hcutoff hσsmall x u s hA Mk hMk hi P hP hMkP hRP hRi hσi hcount
    L hL H step c hstep hH hsubset hdense modulus hm residue hsize hsmall ε hε hmesh
    selection hx hq e εcoef he hεcoef hεe hlarge hperiod v₀ hv₀ outputResidue
    mesh Cmask hmesh0 hmesh1 hscaleMesh hCmask hmask
    center width ideal law proxy href
  have hσ1 : ∀ j, σ j ≤ 1 := fun j => (hσsmall j).trans htone
  have hw := principalProgressionSlice_parameters (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)
    L H step c hL hstep hH hδ hsubset hdense
  have hg := allocatedAffineIdeal_profile_integrable B U basis hR S x rows hRP hRi
    (ρ (allocatedGridAxis (I := I) U basis S.value)) (hρpos _) (hρone _)
    center width (fun i => (hw i).2.2) modulus outputResidue hCmask hmask
  have hlong := allocatedSlicedLongJet_ideal_transfer_withCutoff B U basis hR hσ S x rows d hcutoff
    hMk selection hx hq hrows hcard hσ1 hP he hεcoef hMkP hRP hRi hσi hcount hεe hlarge
    modulus hperiod s hA hi u H step c (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset hm residue hsize
    v₀ hv₀ (allocatedLongProfileDensity B U basis S x rows modulus outputResidue ideal)
    hg (Eref := allocatedAffineSourceReferenceError B U basis S α O
      (ρ (allocatedGridAxis (I := I) U basis S.value)) P η (fun _ => modulus) H ε mesh Cmask) href
  exact hlong

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)
variable (d : ℕ)

def AllocatedAffineCoefficientComparisonWithCutoff
    (δ η : ℝ) (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1) : Prop :=
  ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
        (S : LayerSamplerScale (G := G) B U basis R σ)
        (hcutoff : AllocatedTailCutoffCompatible U basis S.value d),
      ∀ (hσsmall : ∀ j, σ j ≤ t),
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)),
      ∀ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      ∀ {Mk : ℕ} (hMk : 0 < Mk)
        (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j)
          (s j) (hA j) (1 / (Mk : ℝ)))
        {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
        (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (hcount : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P),
      let L := principalAxisLength (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a) (allocatedPrincipalSides B U basis S)
      let hL := fun j : PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) => allocatedPrincipalSides_pos B U basis S
        (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j))
      ∀ (H step : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℕ) (c : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℤ)
        (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
        (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
        (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
        (modulus : ℕ) (hm : 0 < modulus)
        (residue : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → Option α → ZMod modulus)
        (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)
        (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H j) < volume.real (scalarCubeDomain α))
        {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε)
        (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
        (hq : Fintype.card α ≤ d + 1)
        {e εcoef : ℝ} (he : 0 ≤ e) (hεcoef : 0 < εcoef) (hεe : εcoef⁻¹ ≤ Real.exp e)
        (hlarge : Real.exp (allocatedKernelReplacementLogWithCutoff (G := G) B d α O P e) ≤ S.value)
        (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
        (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a) (allocatedPrincipalSides B U basis S))
        (hv₀ : (containedProgressionResidueLaw (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step c hL
          (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0),
      let outputResidue := fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
      ∀ {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
        (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
        (hCmask : 1 ≤ Cmask)
        (hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (outputResidue j) z ∧
          allocatedIntegerKernelMask B U basis S x rows j modulus (outputResidue j) z ≤ Cmask),
      let center := principalProgressionSliceCenter (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L c
      let width := principalProgressionSliceWidth (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step
      let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) => R o.1.val.1)
        (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width)
      let law := containedProgressionResidueLaw (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step c hL
        (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset modulus hm residue hsize
      (∫ z, |law.mean (fun v => allocatedLongJetDensity B U basis hR hσ S x u v rows s hA
            (fun j => (hσsmall j).trans htone) z) -
          allocatedLongProfileDensity B U basis S x rows modulus outputResidue ideal z|
        ∂allocatedLongJetReference B U basis S O) ≤
        (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P) + 1)^
          Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
          (Fintype.card {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} * εcoef *
            (1 + (layerKernelIndexBound (max m d) Mk : ℝ) * Real.exp (allocatedDensityLog (G := G) B α O P) + εcoef)^
              Fintype.card {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}) +
        allocatedAffineSourceReferenceError B U basis S α O
          (ρ (allocatedGridAxis (I := I) U basis S.value)) P η (fun _ => modulus) H ε mesh Cmask

omit [∀ j, Nonempty (O j)] in
include hrows hcard in
theorem allocatedAffineCoefficientComparison_of_reference_withCutoff
    {δ η : ℝ} (hδ : 0 < δ) (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0)
    (hρpos : ∀ P, 0 < ρ P) (hρone : ∀ P, ρ P ≤ 1) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineReferenceComparison.{uJ, _, _, _, _, _} (G := G) B rows δ η ρ t) :
    AllocatedAffineCoefficientComparisonWithCutoff.{uJ, _, _, _, _, _} (G := G) B rows d δ η ρ t htone := by
  unfold AllocatedAffineCoefficientComparisonWithCutoff
  intro J _ U basis R σ hR hσ S hcutoff hσsmall x u s hA Mk hMk hi P hP hMkP hRP hRi hσi hcount
    L hL H step c hstep hH hsubset hdense modulus hm residue hsize hsmall ε hε hmesh
    selection hx hq e εcoef he hεcoef hεe hlarge hperiod v₀ hv₀ outputResidue
    mesh Cmask hmesh0 hmesh1 hscaleMesh hCmask hmask
    center width ideal law
  have hσ1 : ∀ j, σ j ≤ 1 := fun j => (hσsmall j).trans htone
  have href := hs U basis hR hσ S hσsmall x u s hA hMk hi hP hMkP hRP hRi hσi hcount
    L step H (fun _ => modulus) c hL hstep hH hsubset hdense (fun _ _ => modulus) residue
    (fun _ _ => hm) (fun _ _ => le_rfl) hsize hsmall hε hmesh
    modulus outputResidue hmesh0 hmesh1 hscaleMesh hCmask hmask
  with_reducible
    refine allocatedAffineCoefficient_from_reference_l1_withCutoff B rows hrows hcard d hδ ρ hρpos hρone t htone
      U basis hR hσ S hcutoff hσsmall x u s hA hMk hi hP hMkP hRP hRi hσi hcount
      H step c hstep hH hsubset hdense modulus hm residue hsize hsmall hε hmesh
      selection hx hq he hεcoef hεe hlarge hperiod v₀ hv₀ hmesh0 hmesh1 hscaleMesh hCmask hmask ?_
  exact href

include hrows hcard in
theorem exists_early_allocated_affine_coefficient_source_withCutoff
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a)
    (hblock : ∀ a, Function.Injective (block a))
    {δ η : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η) :
    ∃ ρmin : ℝ≥0, 0 < ρmin ∧ ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ P, ρmin ≤ ρ P ∧ ρ P ≤ 1) ∧
      (∀ P, (ρ P : ℝ) = partitionedAffineSourceRadius (B := B)
        (O := fun a : {a // ¬P a} => O a.val.1) (α := α) (layerSamplerDegree I n) P A T (δ / 2) η) ∧
      ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
      t = allocatedAffineSourceTolerance (G := G) (O := O) (α := α) B A T (δ / 2) η ∧
      AllocatedAffineCoefficientComparisonWithCutoff.{uJ, _, _, _, _, _} (G := G) B rows d δ η ρ t htone := by
  obtain ⟨ρmin, hρmin, ρ, hρ, hρeq, t, ht, htone, hteq, hs⟩ :=
    exists_early_allocated_affine_reference_source (G := G) B rows hrows hcard
      ψ hψ hrange hzero hone A T hLip hTransition block hblock hδ hδone hη
  refine ⟨ρmin, hρmin, ρ, hρ, hρeq, t, ht, htone, hteq, ?_⟩
  exact allocatedAffineCoefficientComparison_of_reference_withCutoff B rows hrows hcard d hδ ρ
    (fun P => hρmin.trans_le (hρ P).1) (fun P => (hρ P).2) t htone hs

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory Module Submodule
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)
variable (d : ℕ)

def AllocatedAffineCoveredComparisonWithCutoff
    (δ η : ℝ) (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (_htone : t ≤ 1) : Prop :=
  ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
        (S : LayerSamplerScale (G := G) B U basis R σ)
        (hcutoff : AllocatedTailCutoffCompatible U basis S.value d),
      ∀ (hσsmall : ∀ j, σ j ≤ t),
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)),
      ∀ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      ∀ {Mk : ℕ} (hMk : 0 < Mk)
        (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j)
          (s j) (hA j) (1 / (Mk : ℝ)))
        {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
        (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (hcount : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P),
      let L := principalAxisLength (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a) (allocatedPrincipalSides B U basis S)
      let hL := fun j : PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) => allocatedPrincipalSides_pos B U basis S
        (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j))
      ∀ (H step : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℕ) (c : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℤ)
        (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
        (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
        (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
        (modulus : ℕ) (hm : 0 < modulus)
        (residue : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → Option α → ZMod modulus)
        (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)
        (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H j) < volume.real (scalarCubeDomain α))
        {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε)
        (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
        (hq : Fintype.card α ≤ d + 1)
        {e εcoef : ℝ} (he : 0 ≤ e) (hεcoef : 0 < εcoef) (hεe : εcoef⁻¹ ≤ Real.exp e)
        (hlarge : Real.exp (allocatedKernelReplacementLogWithCutoff (G := G) B d α O P e) ≤ S.value)
        (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
        (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a) (allocatedPrincipalSides B U basis S))
        (hv₀ : (containedProgressionResidueLaw (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step c hL
          (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0),
      let outputResidue := fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
      ∀ {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
        (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
        (hCmask : 1 ≤ Cmask)
        (hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (outputResidue j) z ∧
          allocatedIntegerKernelMask B U basis S x rows j modulus (outputResidue j) z ≤ Cmask),
      let center := principalProgressionSliceCenter (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L c
      let width := principalProgressionSliceWidth (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step
      let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) => R o.1.val.1)
        (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width)
      let law := containedProgressionResidueLaw (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step c hL
        (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset modulus hm residue hsize
      ∀ (Q : Fin m → Type uQ) [∀ j, Fintype (Q j)]
        (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
        (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
        (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
        (deckModulus : ℕ) [NeZero deckModulus]
        (F : AllocatedFrozenCoefficients B U basis S × EuclideanJetLayers U O → ℂ)
        (hF : Measurable F) (hFbound : ∀ p, ‖F p‖ ≤ 1),
      ‖(∫ p, law.complexMean (fun v => F (((allocatedCoefficientSplit B U basis S) p.1).1,
          euclideanCoefficientJetMap U
            (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (principalAxisJoin (allocatedGridAxis (I := I) U basis S.value) u v))
            (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin (allocatedGridAxis (I := I) U basis S.value) u v)) rows
            (canonicalCoefficientDeckSample U bW basis hb o deckModulus (Nat.pos_of_ne_zero (NeZero.ne deckModulus)) p.1 p.2)))
          ∂(allocatedCoefficientSource B U basis hR hσ S).prod
            (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q deckModulus)).toMeasure) -
        ∫ a₀, ∫ z, (allocatedLongProfileDensity B U basis S x rows modulus outputResidue ideal z : ℂ) *
          allocatedCoveredFixedTest B U basis S x u v₀ rows Q hb o bW deckModulus F a₀ z
          ∂allocatedLongJetReference B U basis S O ∂allocatedFrozenCoefficientSource B U basis hR hσ S‖ ≤
        (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P) + 1)^
          Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
          (Fintype.card {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} * εcoef *
            (1 + (layerKernelIndexBound (max m d) Mk : ℝ) * Real.exp (allocatedDensityLog (G := G) B α O P) + εcoef)^
              Fintype.card {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}) +
        allocatedAffineSourceReferenceError B U basis S α O
          (ρ (allocatedGridAxis (I := I) U basis S.value)) P η (fun _ => modulus) H ε mesh Cmask

omit [∀ j, Nonempty (O j)] in
theorem allocatedAffineCoveredComparison_of_coefficient_withCutoff
    {δ η : ℝ} (hδ : 0 < δ) (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0)
    (hρpos : ∀ P, 0 < ρ P) (hρone : ∀ P, ρ P ≤ 1) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineCoefficientComparisonWithCutoff.{uJ, _, _, _, _, _} (G := G) B rows d δ η ρ t htone) :
    AllocatedAffineCoveredComparisonWithCutoff.{uJ, uQ, _, _, _, _, _} (G := G) B rows d δ η ρ t htone := by
  unfold AllocatedAffineCoveredComparisonWithCutoff
  intro J _ U basis R σ hR hσ S hcutoff hσsmall x u s hA Mk hMk hi P hP hMkP hRP hRi hσi hcount
    L hL H step c hstep hH hsubset hdense modulus hm residue hsize hsmall ε hε hmesh
    selection hx hq e εcoef he hεcoef hεe hlarge hperiod v₀ hv₀ outputResidue
    mesh Cmask hmesh0 hmesh1 hscaleMesh hCmask hmask
    center width ideal law
    Q _ hb o bW deckModulus _ F hF hFbound
  have hσ1 : ∀ j, σ j ≤ 1 := fun j => (hσsmall j).trans htone
  have hc := hs U basis hR hσ S hcutoff hσsmall x u s hA hMk hi hP hMkP hRP hRi hσi hcount
    H step c hstep hH hsubset hdense modulus hm residue hsize hsmall hε hmesh
    selection hx hq he hεcoef hεe hlarge hperiod v₀ hv₀
    hmesh0 hmesh1 hscaleMesh hCmask hmask
  have hw := principalProgressionSlice_parameters (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)
    L H step c hL hstep hH hδ hsubset hdense
  have hg := allocatedAffineIdeal_profile_integrable B U basis hR S x rows hRP hRi
    (ρ (allocatedGridAxis (I := I) U basis S.value)) (hρpos _) (hρone _)
    center width (fun i => (hw i).2.2) modulus outputResidue hCmask hmask
  exact allocatedSlicedPhysicalCovered_test_comparison_of_l1 B U basis hR hσ S x u v₀ rows
    Q hb o bW deckModulus s hA hσ1 modulus hperiod F H step c (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j))
    hsubset hm residue hsize hv₀ _ hg hc hF hFbound

include hrows hcard in
theorem exists_early_allocated_affine_covered_source_withCutoff
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a)
    (hblock : ∀ a, Function.Injective (block a))
    {δ η : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η) :
    ∃ ρmin : ℝ≥0, 0 < ρmin ∧ ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ P, ρmin ≤ ρ P ∧ ρ P ≤ 1) ∧
      (∀ P, (ρ P : ℝ) = partitionedAffineSourceRadius (B := B)
        (O := fun a : {a // ¬P a} => O a.val.1) (α := α) (layerSamplerDegree I n) P A T (δ / 2) η) ∧
      ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
      t = allocatedAffineSourceTolerance (G := G) (O := O) (α := α) B A T (δ / 2) η ∧
      AllocatedAffineCoveredComparisonWithCutoff.{uJ, uQ, _, _, _, _, _} (G := G) B rows d δ η ρ t htone := by
  obtain ⟨ρmin, hρmin, ρ, hρ, hρeq, t, ht, htone, hteq, hs⟩ :=
    exists_early_allocated_affine_coefficient_source_withCutoff (G := G) B rows hrows hcard d
      ψ hψ hrange hzero hone A T hLip hTransition block hblock hδ hδone hη
  refine ⟨ρmin, hρmin, ρ, hρ, hρeq, t, ht, htone, hteq, ?_⟩
  exact allocatedAffineCoveredComparison_of_coefficient_withCutoff B rows d hδ ρ
    (fun P => hρmin.trans_le (hρ P).1) (fun P => (hρ P).2) t htone hs

end Erdos3.VectorPolynomial

end

end OAI
