import OAI.Combinatorics.Progressions.Linear.AllocatedFixedKernelReplacement

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def allocatedKernelLogWithCutoff (d : ℕ) (G α : Type*) [Fintype G] [Fintype α]
    {m : ℕ} (O : Fin m → Type*) [∀ j, Fintype (O j)] (P : ℝ) : ℝ :=
  P + ((max m d)*2^((max m d)+1) : ℕ)*P + (Fintype.card α : ℝ)*(m+1) +
    ∑ j, kernelInverseLog (Fintype.card α) (Fintype.card G) (Fintype.card (O j)) (j.val+1) P

theorem allocatedKernelLogWithCutoff_bounds (d : ℕ) (G α : Type*) [Fintype G] [Fintype α]
    {m : ℕ} (O : Fin m → Type*) [∀ j, Fintype (O j)] {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ allocatedKernelLogWithCutoff d G α O P ∧ P ≤ allocatedKernelLogWithCutoff d G α O P ∧
    ((max m d)*2^((max m d)+1) : ℕ)*P ≤ allocatedKernelLogWithCutoff d G α O P ∧
    (Fintype.card α : ℝ)*(m+1) ≤ allocatedKernelLogWithCutoff d G α O P ∧
    ∀ j, kernelInverseLog (Fintype.card α) (Fintype.card G) (Fintype.card (O j)) (j.val+1) P ≤
      allocatedKernelLogWithCutoff d G α O P := by
  have hi (j : Fin m) : 0 ≤ kernelInverseLog
      (Fintype.card α) (Fintype.card G) (Fintype.card (O j)) (j.val+1) P := by
    unfold kernelInverseLog
    positivity
  have hs := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hi j)
  have hidx : 0 ≤ ((max m d)*2^((max m d)+1) : ℕ)*(P : ℝ) := by positivity
  have hentry : 0 ≤ (Fintype.card α : ℝ)*(m+1) := by positivity
  unfold allocatedKernelLogWithCutoff
  refine ⟨by positivity, by linarith, by linarith, by linarith, ?_⟩
  intro j
  have hj := Finset.single_le_sum (fun k _ => hi k) (Finset.mem_univ j)
  linarith

theorem allocatedKernelLogWithCutoff_allowances (d : ℕ) (G α : Type*) [Fintype G] [Fintype α]
    {m : ℕ} (O : Fin m → Type*) [∀ j, Fintype (O j)] {P : ℝ} {M : ℕ}
    (hP : 0 ≤ P) (hM : 0 < M) (hMP : (M : ℝ) ≤ Real.exp P) :
    (layerKernelIndexBound (max m d) M : ℝ) ≤ Real.exp (allocatedKernelLogWithCutoff d G α O P) ∧
    ∀ j, kernelJetEntryAllowance (Fintype.card α) (j.val+1) ≤ Real.exp (allocatedKernelLogWithCutoff d G α O P) ∧
      kernelJetInverseAllowance (Fintype.card α) (Fintype.card G) (Fintype.card (O j)) (j.val+1)
        (1/(M : ℝ)) ≤ Real.exp (allocatedKernelLogWithCutoff d G α O P) := by
  have hb := allocatedKernelLogWithCutoff_bounds d G α O hP
  refine ⟨(layerKernelIndexBound_le_exp (max m d) hMP).trans (Real.exp_le_exp.mpr hb.2.2.1), ?_⟩
  intro j
  constructor
  · apply (kernelJetEntryAllowance_le_exp (Fintype.card α) (j.val+1)).trans
    apply Real.exp_le_exp.mpr
    apply le_trans _ hb.2.2.2.1
    gcongr
    exact_mod_cast Nat.succ_le_of_lt j.isLt
  · have hκ : 0 < 1/(M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
    have hv := kernelJetInverseAllowance_le_exp (Fintype.card α) (Fintype.card G)
      (Fintype.card (O j)) (j.val+1) hκ hP (by simpa only [one_div, inv_inv] using hMP)
    exact hv.trans (Real.exp_le_exp.mpr (hb.2.2.2.2 j))

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedKernelReplacementLogWithCutoff (d : ℕ) (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] (P e : ℝ) : ℝ :=
  ∑ j, coefficientFrontLog (Fintype.card (O j))
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))
    (allocatedKernelLogWithCutoff d G α O P) (4*(P+8)) e

theorem allocatedKernelReplacementLogWithCutoff_front_le (d : ℕ) (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] {P e : ℝ} (hP : 0 ≤ P) (he : 0 ≤ e) (j : Fin m) :
    coefficientFrontLog (Fintype.card (O j))
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))
      (allocatedKernelLogWithCutoff d G α O P) (4*(P+8)) e ≤ allocatedKernelReplacementLogWithCutoff (G := G) B d α O P e := by
  apply Finset.single_le_sum _ (Finset.mem_univ j)
  intro k _
  exact coefficientFrontLog_nonneg _ _ (allocatedKernelLogWithCutoff_bounds d G α O hP).1 (by positivity) he

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

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

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

theorem allocatedFixedKernel_replacement_withCutoff (d : ℕ)
    (hcutoff : AllocatedTailCutoffCompatible U basis S.value d) {M : ℕ} (hM : 0 < M)
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
    (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ))) :
    ∀ (u : PrincipalAxisTuples (α := α) grid sides)
        (p : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
        (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
      (∀ v, p.weight v ≠ 0 → ∀ j,
        integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v) modulus = residue j) →
      ∀ j i (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i),
      (∀ z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
        allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ layerKernelIndexBound (max m d) M) ∧
      ∀ v, p.weight v ≠ 0 → ∀ z,
        |(basisAxisScale (basis j) i : ℝ)^Fintype.card (O j) *
            (allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i (hσ1 j) henormous z).toReal -
          allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z *
            allocatedIntegerKernelDensity B U basis S j i x u (rows j) (s j) (hA j)
              (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v)
              (fun o => (z o : ℝ)/(basisAxisScale (basis j) i : ℝ))| ≤ ε := by
  have hκ : 0 < 1/(M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  have hcontrol := allocatedFixedKernel_controls_withCutoff B U basis S x rows d selection hx hq hinj hrows s hA hi
  intro u p residue hr j i henormous
  have hb := allocatedKernelLogWithCutoff_bounds d G α O hP
  have ha := allocatedKernelLogWithCutoff_allowances d G α O hP hM hMP
  have ht : 0 ≤ 4*(P+8) := by positivity
  have hf := (Real.exp_le_exp.mpr (allocatedKernelReplacementLogWithCutoff_front_le (G := G) B d α O hP he j)).trans hlarge
  exact allocatedIntegerKernel_residue_family B U basis hR hσ S x u rows j i (s j) (hA j) (hσ1 j)
    henormous p modulus (residue j) (hperiod j) (fun v hv => hr v hv j)
    (kernelJetEntryAllowance_pos _ _).le (kernelJetInverseAllowance_nonneg _ _ _ _ hκ)
    (Nat.cast_nonneg _) (fun v _ => hcontrol u v j i)
    hb.1 ht hε ha.1 (ha.2 j).2 (ha.2 j).1 ((hRP j).trans (Real.exp_le_exp.mpr hb.2.1))
    (allocatedUnitProfileWidth_inverse_exp _ hP (hR j) (hσ j) (hRi j) (hσi j) (hcount j))
    (allocatedInteger_replacementScale_le_withCutoff B U basis S d j i (rows j) (hinj j) hq (s j)
      hb.1 ht he hε hεe hf (hcutoff j i henormous))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

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

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

theorem allocatedGoodKernel_replacement_withCutoff (d : ℕ)
    (hcutoff : AllocatedTailCutoffCompatible U basis S.value d) {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ d+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P e ε : ℝ} (hP : 0 ≤ P) (he : 0 ≤ e) (hε : 0 < ε)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hεe : ε⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLogWithCutoff (G := G) B d α O P e) ≤ S.value) :
    ∃ (modulus : ℕ) (_hm : 0 < modulus), modulus ≤ M^(m+1) ∧
      (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
      (∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
        (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range) ∧
      ∃ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0),
      (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ))) ∧
      ∀ (u : PrincipalAxisTuples (α := α) grid sides)
        (p : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
        (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
      (∀ v, p.weight v ≠ 0 → ∀ j,
        integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v) modulus = residue j) →
      ∀ j i (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i),
      (∀ z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
        allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ layerKernelIndexBound (max m d) M) ∧
      ∀ v, p.weight v ≠ 0 → ∀ z,
        |(basisAxisScale (basis j) i : ℝ)^Fintype.card (O j) *
            (allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i (hσ1 j) henormous z).toReal -
          allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z *
            allocatedIntegerKernelDensity B U basis S j i x u (rows j) (s j) (hA j)
              (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v)
              (fun o => (z o : ℝ)/(basisAxisScale (basis j) i : ℝ))| ≤ ε := by
  have hκ : 0 < 1/(M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  obtain ⟨modulus, hm, hmB, hspatial, hperiod⟩ := goodKernel_common_period selection x hx (m+1)
    (Nat.succ_le_succ (Nat.zero_le m)) (fun j : Fin m => j.val+1)
    (fun j => (Nat.succ_le_of_lt j.isLt).trans (Nat.le_succ _)) rows hinj hrows
  obtain ⟨s, hA, hi, _⟩ := allocatedGoodKernel_controls_withCutoff B U basis S x rows d
    selection hκ hx hq hinj hrows
  exact ⟨modulus, hm, hmB, hspatial, hperiod, s, hA, hi,
    allocatedFixedKernel_replacement_withCutoff B U basis hR hσ S x rows d hcutoff hM
      selection hx hq hinj hrows hσ1 hP he hε hMP hRP hRi hσi hcount hεe hlarge
      modulus hperiod s hA hi⟩

end Erdos3.VectorPolynomial

end

end OAI
