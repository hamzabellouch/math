import Mathlib
import OAI.RepresentationTheory.RestrictedTilting.ExtensionSplitting
import OAI.RepresentationTheory.RestrictedTilting.TensorLimits

namespace OAI

/-! Binary multiplication exact sequences and tensor closure of good filtrations. -/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof
section

universe u
variable (k : Type u) [Field k]
open scoped TensorProduct

abbrev BiBinary (a b : ℕ) := Binary k a ⊗[k] Binary k b
abbrev BiPolynomial := MvPolynomial (Fin 2) k ⊗[k] MvPolynomial (Fin 2) k

noncomputable instance biBinaryAddCommGroup (a b : ℕ) : AddCommGroup (BiBinary k a b) :=
  TensorProduct.addCommGroup

noncomputable def binaryMulX (n : ℕ) (i : Fin 2) : Binary k n →ₗ[k] Binary k (n + 1) where
  toFun f := ⟨MvPolynomial.X i * f.val,
    by simpa [Nat.add_comm] using (MvPolynomial.isHomogeneous_X k i).mul f.property⟩
  map_add' f g := by apply Subtype.ext; simp [mul_add]
  map_smul' c f := by apply Subtype.ext; simp

noncomputable def biBinaryEmbed (a b : ℕ) : BiBinary k a b →ₗ[k] BiPolynomial k :=
  TensorProduct.map (Binary k a).subtype (Binary k b).subtype

lemma biBinaryEmbed_injective (a b : ℕ) : Function.Injective (biBinaryEmbed k a b) :=
  TensorProduct.map_injective_of_flat_flat _ _
    (Binary k a).injective_subtype (Binary k b).injective_subtype

 
noncomputable def determinantMap (a b : ℕ) : BiBinary k a b →ₗ[k] BiBinary k (a + 1) (b + 1) :=
  TensorProduct.map (binaryMulX k a 0) (binaryMulX k b 1) -
    TensorProduct.map (binaryMulX k a 1) (binaryMulX k b 0)

noncomputable def biDeterminant : BiPolynomial k :=
  MvPolynomial.X 0 ⊗ₜ[k] MvPolynomial.X 1 - MvPolynomial.X 1 ⊗ₜ[k] MvPolynomial.X 0

lemma embed_determinantMap (a b : ℕ) (x : BiBinary k a b) :
    biBinaryEmbed k (a + 1) (b + 1) (determinantMap k a b x) =
      biDeterminant k * biBinaryEmbed k a b x := by
  induction x using TensorProduct.inductionOn with
  | tmul f g =>
    simp only [biBinaryEmbed, determinantMap, LinearMap.sub_apply, TensorProduct.map_tmul,
      map_sub, biDeterminant, sub_mul, Algebra.TensorProduct.tmul_mul_tmul]
    rfl
  | add x y hx hy => simp [map_add, hx, hy, mul_add]

lemma biDeterminant_ne_zero :
    MvPolynomial.tensorEquivSum k (Fin 2) (Fin 2) k (biDeterminant k) ≠ 0 := by
  intro h
  have hh := congrArg
    (MvPolynomial.eval (fun i : Fin 2 ⊕ Fin 2 => match i with
      | .inl i => if i = 0 then (1 : k) else 0
      | .inr i => if i = 1 then (1 : k) else 0)) h
  simp [biDeterminant] at hh

lemma determinantMap_injective (a b : ℕ) : Function.Injective (determinantMap k a b) := by
  intro x y hxy
  apply biBinaryEmbed_injective k a b
  apply (MvPolynomial.tensorEquivSum k (Fin 2) (Fin 2) k).injective
  apply mul_left_cancel₀ (biDeterminant_ne_zero k)
  rw [← map_mul, ← map_mul, ← embed_determinantMap, ← embed_determinantMap, hxy]

noncomputable def binaryMultiply (a b : ℕ) : BiBinary k a b →ₗ[k] Binary k (a + b) :=
  TensorProduct.lift
    { toFun := fun f =>
        { toFun := fun g => ⟨f.val * g.val, f.property.mul g.property⟩
          map_add' := by intro g h; apply Subtype.ext; simp [mul_add]
          map_smul' := by intro c g; apply Subtype.ext; simp }
      map_add' := by intro f g; ext h : 1; apply Subtype.ext; simp [add_mul]
      map_smul' := by intro c f; ext g : 1; apply Subtype.ext; simp }

@[simp] lemma binaryMultiply_tmul (a b : ℕ) (f : Binary k a) (g : Binary k b) :
    (binaryMultiply k a b (f ⊗ₜ[k] g)).val = f.val * g.val := rfl

lemma binaryMultiply_determinantMap (a b : ℕ) :
    (binaryMultiply k (a + 1) (b + 1)).comp (determinantMap k a b) = 0 := by
  apply TensorProduct.ext'
  intro f g
  apply Subtype.ext
  simp only [LinearMap.comp_apply, determinantMap, LinearMap.sub_apply, TensorProduct.map_tmul,
    map_sub, Submodule.coe_sub, binaryMultiply_tmul]
  change (MvPolynomial.X 0 * f.val) * (MvPolynomial.X 1 * g.val) -
    (MvPolynomial.X 1 * f.val) * (MvPolynomial.X 0 * g.val) = 0
  ring

lemma binaryMultiply_surjective (a b : ℕ) : Function.Surjective (binaryMultiply k a b) := by
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← (binaryBasis k (a + b)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  let j : Fin (a + 1) := ⟨min i.val a, by omega⟩
  let l : Fin (b + 1) := ⟨i.val - j.val, by dsimp [j]; omega⟩
  refine ⟨binaryBasis k a j ⊗ₜ[k] binaryBasis k b l, ?_⟩
  apply Subtype.ext
  simp only [binaryMultiply_tmul, binaryBasis_apply]
  have h₁ : a - j.val + (b - l.val) = a + b - i.val := by dsimp [j, l]; omega
  have h₂ : j.val + l.val = i.val := by dsimp [j, l]; omega
  rw [mul_mul_mul_comm, ← pow_add, ← pow_add, h₁, h₂]

lemma binaryMultiply_exact (a b : ℕ) :
    LinearMap.range (determinantMap k a b) = LinearMap.ker (binaryMultiply k (a + 1) (b + 1)) := by
  have hin : LinearMap.range (determinantMap k a b) ≤
      LinearMap.ker (binaryMultiply k (a + 1) (b + 1)) := by
    rw [LinearMap.range_le_ker_iff]
    exact binaryMultiply_determinantMap k a b
  have : FiniteDimensional k (Binary k a) := Module.Finite.of_basis (binaryBasis k a)
  have : FiniteDimensional k (Binary k b) := Module.Finite.of_basis (binaryBasis k b)
  have : FiniteDimensional k (Binary k (a + 1)) := Module.Finite.of_basis (binaryBasis k (a + 1))
  have : FiniteDimensional k (Binary k (b + 1)) := Module.Finite.of_basis (binaryBasis k (b + 1))
  apply Submodule.eq_of_le_of_finrank_eq hin
  have hr := LinearMap.finrank_range_of_inj (determinantMap_injective k a b)
  have hn := LinearMap.finrank_range_add_finrank_ker (binaryMultiply k (a + 1) (b + 1))
  rw [LinearMap.range_eq_top.mpr (binaryMultiply_surjective k (a + 1) (b + 1)),
    finrank_top] at hn
  rw [Module.finrank_tensorProduct, binaryBasis_finrank, binaryBasis_finrank] at hr hn
  rw [binaryBasis_finrank] at hn
  nlinarith




noncomputable def biLinearChange (A : Matrix (Fin 2) (Fin 2) k) :
    BiPolynomial k →ₐ[k] BiPolynomial k :=
  Algebra.TensorProduct.map (linearChange A) (linearChange A)

lemma biLinearChange_determinant (A : Matrix (Fin 2) (Fin 2) k) :
    biLinearChange k A (biDeterminant k) = A.det • biDeterminant k := by
  apply (MvPolynomial.tensorEquivSum k (Fin 2) (Fin 2) k).injective
  simp only [biLinearChange, biDeterminant, map_sub, Algebra.TensorProduct.map_tmul,
    linearChange_X, Fin.sum_univ_two, ← MvPolynomial.smul_eq_C_mul,
    TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.smul_tmul_smul,
    map_add, map_smul, MvPolynomial.tensorEquivSum_X_tmul_X]
  simp only [MvPolynomial.smul_eq_C_mul, Matrix.det_fin_two, map_mul, map_sub]
  ring

noncomputable def biBinaryAction (a b : ℕ) (A : Matrix (Fin 2) (Fin 2) k) :
    BiBinary k a b →ₗ[k] BiBinary k a b :=
  TensorProduct.map (homogeneousRepresentation a A) (homogeneousRepresentation b A)

lemma biBinaryEmbed_action (a b : ℕ) (A : Matrix (Fin 2) (Fin 2) k) (x : BiBinary k a b) :
    biBinaryEmbed k a b (biBinaryAction k a b A x) =
      biLinearChange k A (biBinaryEmbed k a b x) := by
  induction x using TensorProduct.inductionOn with
  | tmul f g => rfl
  | add x y hx hy => simp [hx, hy]

lemma determinantMap_equivariant (a b : ℕ) (A : Matrix (Fin 2) (Fin 2) k)
    (hA : A.det = 1) (x : BiBinary k a b) :
    determinantMap k a b (biBinaryAction k a b A x) =
      biBinaryAction k (a + 1) (b + 1) A (determinantMap k a b x) := by
  apply biBinaryEmbed_injective k (a + 1) (b + 1)
  rw [embed_determinantMap, biBinaryEmbed_action, biBinaryEmbed_action,
    embed_determinantMap, map_mul, biLinearChange_determinant, hA, one_smul]

lemma binaryMultiply_equivariant (a b : ℕ) (A : Matrix (Fin 2) (Fin 2) k)
    (x : BiBinary k a b) :
    binaryMultiply k a b (biBinaryAction k a b A x) =
      homogeneousRepresentation (a + b) A (binaryMultiply k a b x) := by
  induction x using TensorProduct.inductionOn with
  | tmul f g =>
    apply Subtype.ext
    change linearChange A f.val * linearChange A g.val = linearChange A (f.val * g.val)
    exact (map_mul _ _ _).symm
  | add x y hx hy => simp [hx, hy]

lemma dualMatrix_det (g : SL2 k) : (dualMatrix k g).det = 1 := by
  change Matrix.det ((g⁻¹ : SL2 k).val.transpose) = 1
  rw [Matrix.det_transpose]
  exact (g⁻¹ : SL2 k).property

end

universe u
variable (k : Type u) [Field k]
noncomputable def costandardDeterminant (a b : ℕ) :
    costandard k a ⊗ costandard k b ⟶ costandard k (a + 1) ⊗ costandard k (b + 1) :=
  fdrepHom k (determinantMap k a b) (fun g x =>
    determinantMap_equivariant k a b (dualMatrix k g) (dualMatrix_det k g) x)

 
noncomputable def costandardMultiply (a b : ℕ) :
    costandard k a ⊗ costandard k b ⟶ costandard k (a + b) :=
  fdrepHom k (binaryMultiply k a b) (fun g x =>
    binaryMultiply_equivariant k a b (dualMatrix k g) x)

lemma costandardDeterminant_multiply (a b : ℕ) :
    costandardDeterminant k a b ≫ costandardMultiply k (a + 1) (b + 1) = 0 := by
  apply Action.hom_ext
  apply FGModuleCat.hom_ext
  exact binaryMultiply_determinantMap k a b

 
noncomputable def costandardTensorSequence (a b : ℕ) : ShortComplex (FDRep k (SL2 k)) :=
  ShortComplex.mk (costandardDeterminant k a b) (costandardMultiply k (a + 1) (b + 1))
    (costandardDeterminant_multiply k a b)

lemma costandardTensorSequence_shortExact (a b : ℕ) :
    (costandardTensorSequence k a b).ShortExact :=
  fdrep_shortExact k _ (determinantMap_injective k a b)
    (binaryMultiply_surjective k (a + 1) (b + 1)) (binaryMultiply_exact k a b)


lemma costandardMultiply_isIso_of_zero (a b : ℕ) (h : a = 0 ∨ b = 0) :
    IsIso (costandardMultiply k a b) := by
  let F := fdrepForget k (SL2 k)
  have hr : Module.finrank k (BiBinary k a b) = Module.finrank k (Binary k (a + b)) := by
    rw [Module.finrank_tensorProduct, binaryBasis_finrank, binaryBasis_finrank,
      binaryBasis_finrank]
    rcases h with rfl | rfl <;> simp
  have hi : Function.Injective (binaryMultiply k a b) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hr).mpr
      (binaryMultiply_surjective k a b)
  have : Mono (F.map (costandardMultiply k a b)) :=
    (ModuleCat.mono_iff_injective _).mpr hi
  have : Epi (F.map (costandardMultiply k a b)) :=
    (ModuleCat.epi_iff_surjective _).mpr (binaryMultiply_surjective k a b)
  have : Mono (costandardMultiply k a b) := F.mono_of_mono_map (by infer_instance)
  have : Epi (costandardMultiply k a b) := F.epi_of_epi_map (by infer_instance)
  exact isIso_of_mono_of_epi (costandardMultiply k a b)

 

theorem costandard_tensor_hasGoodFiltration (a b : ℕ) :
    HasGoodFiltration k (costandard k a ⊗ costandard k b) := by
  induction a generalizing b with
  | zero =>
    have := costandardMultiply_isIso_of_zero k 0 b (Or.inl rfl)
    exact (costandard_hasGoodFiltration k (0 + b)).of_iso k
      (asIso (costandardMultiply k 0 b)).symm
  | succ a ih =>
    cases b with
    | zero =>
      have := costandardMultiply_isIso_of_zero k (a + 1) 0 (Or.inr rfl)
      exact (costandard_hasGoodFiltration k (a + 1 + 0)).of_iso k
        (asIso (costandardMultiply k (a + 1) 0)).symm
    | succ b =>
      exact .step _ (costandardDeterminant k a b)
        (costandardMultiply k (a + 1) (b + 1)) (costandardDeterminant_multiply k a b)
        (costandardTensorSequence_shortExact k a b) (ih b)


lemma HasGoodFiltration.tensor_costandard {A : FDRep k (SL2 k)}
    (hA : HasGoodFiltration k A) (n : ℕ) :
    HasGoodFiltration k (A ⊗ costandard k n) := by
  induction hA with
  | zero A hA => exact .zero _ ((tensorRight (costandard k n)).map_isZero hA)
  | @step A B m f g w hS hA ih =>
    let := tensorRight_preservesFiniteLimits (costandard k n)
    let := tensorRight_preservesFiniteColimits (costandard k n)
    have hT := hS.map_of_exact (tensorRight (costandard k n))
    exact ih.extension k (costandard_tensor_hasGoodFiltration k m n)
      _ _ _ hT

 
theorem HasGoodFiltration.tensor {A B : FDRep k (SL2 k)}
    (hA : HasGoodFiltration k A) (hB : HasGoodFiltration k B) :
    HasGoodFiltration k (A ⊗ B) := by
  induction hB with
  | zero B hB => exact .zero _ ((tensorLeft A).map_isZero hB)
  | @step B C n f g w hS hB ih =>
    let := tensorLeft_preservesFiniteLimits A
    let := tensorLeft_preservesFiniteColimits A
    have hT := hS.map_of_exact (tensorLeft A)
    exact ih.extension k (hA.tensor_costandard k n) _ _ _ hT

noncomputable def fdrepBidual (A : FDRep k (SL2 k)) : A ≅ (Aᘁ)ᘁ :=
  (rightDualIso
    (@HasRightDual.exact _ _ _ (Aᘁ) (RightRigidCategory.rightDual (Aᘁ)))
    (BraidedCategory.exactPairing_swap A (Aᘁ))).symm

lemma IsRational.of_iso {A B : FDRep k (SL2 k)}
    (h : IsRational k A.ρ) (e : A ≅ B) : IsRational k B.ρ :=
  h.of_surjective k A.ρ B.ρ (fdrepLinear k e.hom) (fdrep_surjective k e.hom)
    (fdrepLinear_comm k e.hom)

lemma IsTilting.of_iso {A B : FDRep k (SL2 k)}
    (h : IsTilting k A) (e : A ≅ B) : IsTilting k B := by
  refine ⟨h.1.of_iso k e, h.2.1.of_iso k e, ?_⟩
  let eD : Aᘁ ≅ Bᘁ :=
    { hom := e.invᘁ
      inv := e.homᘁ
      hom_inv_id := by rw [← comp_rightAdjointMate, e.hom_inv_id, rightAdjointMate_id]
      inv_hom_id := by rw [← comp_rightAdjointMate, e.inv_hom_id, rightAdjointMate_id] }
  exact h.2.2.of_iso k eD

 
theorem IsTilting.tensor {A B : FDRep k (SL2 k)}
    (hA : IsTilting k A) (hB : IsTilting k B) : IsTilting k (A ⊗ B) := by
  refine ⟨IsRational.tensor k A.ρ B.ρ hA.1 hB.1, hA.2.1.tensor k hB.2.1, ?_⟩
  exact (hB.2.2.tensor k hA.2.2).of_iso k (rightDualTensorIso A B).symm

 
theorem IsTilting.dual {A : FDRep k (SL2 k)} (hA : IsTilting k A) : IsTilting k Aᘁ :=
  ⟨by rw [fdrep_dual_repr]; exact IsRational.dual k A.ρ hA.1,
   hA.2.2, hA.2.1.of_iso k (fdrepBidual k A)⟩

end FiberFunctorProof
end

end OAI
