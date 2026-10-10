import OAI.Algebra.Finitistic.Bar.MultibarDecomposition
import Mathlib.Data.Fintype.Vector

namespace OAI
open scoped TensorProduct DirectSum
open TensorProduct TrivSqZeroExt CategoryTheory
noncomputable section

namespace DerivedBar.Multibar.Indexed
universe u

/-- The degree-indexed shapes faithfully record their D/X words. -/
theorem toList_injective {n r : ℕ} : Function.Injective (@toList n r) := by
  intro p
  induction p with
  | nil => intro q h; cases q; rfl
  | base p ih =>
    intro q h
    cases q with
    | base q => exact congrArg Shape.base (ih (List.cons.inj h).2)
    | ideal q => exact Bool.noConfusion (List.cons.inj h).1
  | ideal p ih =>
    intro q h
    cases q with
    | base q => exact Bool.noConfusion (List.cons.inj h).1
    | ideal q => exact congrArg Shape.ideal (ih (List.cons.inj h).2)

/-- The block direct sum is finite in every degree, without any completion. -/
instance shape_finite (n r : ℕ) : Finite (Shape n r) :=
  @Finite.of_injective (Shape n r) (List.Vector Bool n) _ (fun p => (⟨toList p, length_toList p⟩ : List.Vector Bool n))
    (fun _ _ h => toList_injective (congrArg Subtype.val h))

variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

omit [Module D X] [Module Dᵐᵒᵖ X] [SMulCommClass D Dᵐᵒᵖ X]
  [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X] in
/-- The indexed tensor is exactly the earlier literal D/X pattern tensor. -/
theorem tensor_toList {n r : ℕ} (p : Shape n r) :
    tensor k D X N p = patternTerm k D X N (toList p) := by
  induction p with
  | nil => rfl
  | base p ih => exact congrArg (fun V : ModuleCat k => ModuleCat.of k (D ⊗[k] V)) ih
  | ideal p ih => exact congrArg (fun V : ModuleCat k => ModuleCat.of k (X ⊗[k] V)) ih

/-- The sign involution acts by the prescribed inversion count on each tensor summand. -/
theorem inclusion_sign {n r : ℕ} (p : Shape n r) (v : tensor k D X N p) :
    SquareZero.signedProjection k D X N n r (inclusion k D X N p v) =
      (-1 : k)^(inversions (toList p)) • inclusion k D X N p v := by
  induction p with
  | nil => simp only [inclusion, toList, inversions, pow_zero, one_smul,
      SquareZero.signedProjection, LinearMap.id_apply]
  | @base n r p ih =>
    induction v using TensorProduct.inductionOn with
    | tmul d v =>
      change SquareZero.signedProjection k D X N (n+1) r
        ((inl d : TrivSqZeroExt D X) ⊗ₜ[k] inclusion k D X N p v) = _
      rw [SquareZero.signedProjection_base, ih, TensorProduct.tmul_smul, smul_smul,
        ← pow_add]
      simp only [toList, inversions, count_toList]
      rfl
    | add v w hv hw => simp only [map_add, hv, hw, smul_add]
  | @ideal n r p ih =>
    induction v using TensorProduct.inductionOn with
    | tmul x v =>
      change SquareZero.signedProjection k D X N (n+1) (r+1)
        ((inr x : TrivSqZeroExt D X) ⊗ₜ[k] inclusion k D X N p v) = _
      rw [SquareZero.signedProjection_ideal_succ, ih, TensorProduct.tmul_smul]
      rfl
    | add v w hv hw => simp only [map_add, hv, hw, smul_add]

theorem outerInclusion_sign {n r : ℕ} (p : Shape n r) (v : outerTensor k D X N p) :
    SquareZero.twoSidedSignedProjection k D X N n r (outerInclusion k D X N p v) =
      (-1 : k)^(inversions (toList p)) • outerInclusion k D X N p v := by
  induction v using TensorProduct.inductionOn with
  | tmul d v =>
    change d ⊗ₜ[k] SquareZero.signedProjection k D X N n r (inclusion k D X N p v) = _
    rw [inclusion_sign, TensorProduct.tmul_smul]
    rfl
  | add v w hv hw => simp only [map_add, hv, hw, smul_add]

/-- Summation of genuine tensor blocks followed by the source's sign rescaling. -/
def signedAssembly (n r : ℕ) : (⨁ p : Shape n r, outerTensor k D X N p) ≃ₗ[D]
    SquareZero.twoSidedWeight k D X N n r :=
  (decomposition k D X N n r).trans (SquareZero.signEquiv k D X N n r)

variable [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]
variable (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = 0)

/-- Transport of the actual count differential to signed tensor blocks. -/
def blockDifferential (n r : ℕ) :
    (⨁ p : Shape (n+1) r, outerTensor k D X N p) →ₗ[D]
      (⨁ p : Shape n r, outerTensor k D X N p) :=
  (signedAssembly k D X N n r).symm.toLinearMap.comp
    (((SquareZero.twoSidedWeightComplex k D X N hN r).d (n+1) n).hom.comp
      (signedAssembly k D X N (n+1) r).toLinearMap)

theorem blockDifferential_sq (n r : ℕ) :
    (blockDifferential k D X N hN n r).comp (blockDifferential k D X N hN (n+1) r) = 0 := by
  apply LinearMap.ext
  intro z
  change (signedAssembly k D X N n r).symm
    (((SquareZero.twoSidedWeightComplex k D X N hN r).d (n+1) n).hom
      (signedAssembly k D X N (n+1) r
        ((signedAssembly k D X N (n+1) r).symm
          (((SquareZero.twoSidedWeightComplex k D X N hN r).d (n+1+1) (n+1)).hom
            (signedAssembly k D X N (n+1+1) r z))))) = 0
  erw [LinearEquiv.apply_symm_apply]
  have h := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp
    ((SquareZero.twoSidedWeightComplex k D X N hN r).d_comp_d (n+1+1) (n+1) n))
      (signedAssembly k D X N (n+1+1) r z)
  change ((SquareZero.twoSidedWeightComplex k D X N hN r).d (n+1) n).hom
    (((SquareZero.twoSidedWeightComplex k D X N hN r).d (n+1+1) (n+1)).hom
      (signedAssembly k D X N (n+1+1) r z)) = 0 at h
  change (signedAssembly k D X N n r).symm _ = 0
  exact (congrArg (signedAssembly k D X N n r).symm h).trans
    (map_zero (signedAssembly k D X N n r).symm)

/-- Signed block chain model, still indexed by the full homological degree r+Σiⱼ. -/
def signedBlockComplex (r : ℕ) : ChainComplex (ModuleCat D) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of D (⨁ p : Shape n r, outerTensor k D X N p))
    (fun n => ModuleCat.ofHom (blockDifferential k D X N hN n r))
    (fun n => ModuleCat.hom_ext (blockDifferential_sq k D X N hN n r))

/-- Chain isomorphism between the signed block model and the preserved count subcomplex. -/
def signedBlockIso (r : ℕ) : signedBlockComplex k D X N hN r ≅
    SquareZero.twoSidedWeightComplex k D X N hN r :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (signedAssembly k D X N n r).toModuleIso)
    (by
      intro i j hij
      change j+1 = i at hij
      subst i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      simp only [LinearEquiv.toModuleIso_hom, signedBlockComplex, ChainComplex.of_d]
      change ((SquareZero.twoSidedWeightComplex k D X N hN r).d (j+1) j).hom
          (signedAssembly k D X N (j+1) r v) =
        signedAssembly k D X N j r (blockDifferential k D X N hN j r v)
      exact (LinearEquiv.apply_symm_apply (signedAssembly k D X N j r) _).symm)
end DerivedBar.Multibar.Indexed

end

end OAI
