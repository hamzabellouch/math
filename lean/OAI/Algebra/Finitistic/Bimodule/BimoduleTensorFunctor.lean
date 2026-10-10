import OAI.Algebra.Finitistic.Bimodule.BimoduleBalancedTensor

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.BimoduleBalancedTensor
open ExternalTensor.Section4
attribute [local instance] inputEnveloping
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (M : ModuleCat.{u} (Enveloping k B))
variable (N : Type u) [AddCommGroup N] [Module k N] [Module B N]

theorem algebraMap_smul (c : k) (x : Tensor k B M N) :
    algebraMap k B c • x = c • x := by
  induction x using BalancedTensor.induction_on with
  | hz => simp
  | ht m n =>
    rw [smul_mk]
    have he : (algebraMap k B c ⊗ₜ[k] (1 : Bᵐᵒᵖ)) =
        algebraMap k (Enveloping k B) c :=
      (Algebra.TensorProduct.includeLeft : B →ₐ[k] Enveloping k B).commutes c
    rw [he]
    have hm : algebraMap k (Enveloping k B) c • (m : M) = (c • m : Input k B M) := by
      change algebraMap k (Enveloping k B) c • (m : M) =
        BimoduleVertex.restriction k B (algebraMap k Bᵐᵒᵖ c) • (m : M)
      rw [show BimoduleVertex.restriction k B (algebraMap k Bᵐᵒᵖ c) =
        algebraMap k (Enveloping k B) c from
        (Algebra.TensorProduct.includeRight : Bᵐᵒᵖ →ₐ[k] Enveloping k B).commutes c]
    rw [hm]
    exact LinearMap.congr_fun ((BalancedTensor.mk k B (Input k B M) N).map_smul c m) n
  | ha x y hx hy => simp_all [smul_add]

instance scalarTower : IsScalarTower k B (Tensor k B M N) :=
  IsScalarTower.of_algebraMap_smul (algebraMap_smul k B M N)

variable {M} {M' : ModuleCat.{u} (Enveloping k B)}
/-- A genuine bimodule map induces a map preserving the full left B action after tensoring. -/
def map (f : M ⟶ M') : Tensor k B M N →ₗ[B] Tensor k B M' N where
  __ := (BalancedTensor.mapLeft (k := k) N ((forgetRight k B).map f).hom).toAddMonoidHom
  map_smul' b x := by
    induction x using BalancedTensor.induction_on with
    | hz =>
      rw [smul_zero]
      exact (map_zero _).trans
        ((congrArg (b • ·) (map_zero _)).trans (smul_zero b)).symm
    | ht m n =>
      change BalancedTensor.mk k B (Input k B M') N (f.hom
        ((b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (m : M))) n =
        BalancedTensor.mk k B (Input k B M') N
          ((b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • f.hom m) n
      exact congrArg (fun m' => BalancedTensor.mk k B (Input k B M') N m' n)
        (f.hom.map_smul (b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) (m : M))
    | ha x y hx hy =>
      rw [smul_add]
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans
        ((smul_add b _ _).symm.trans (congrArg (b • ·) (map_add _ _ _).symm)))

/-- The actual balanced tensor functor from bimodules to left modules. -/
def functor : ModuleCat.{u} (Enveloping k B) ⥤ ModuleCat.{u} B where
  obj M := ModuleCat.of B (Tensor k B M N)
  map f := ModuleCat.ofHom (map k B N f)
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => rfl
    | ha x y hx hy =>
      exact (map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => rfl
    | ha x y hx hy =>
      exact (map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

instance additive : (functor k B N).Additive where
  map_add := by
    intros M M' f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | hz =>
      exact (map_zero _).trans (map_zero _).symm
    | ht m n =>
      change BalancedTensor.mk k B (Input k B M') N (f.hom m + g.hom m) n = _
      exact LinearMap.congr_fun ((BalancedTensor.mk k B (Input k B M') N).map_add _ _) n
    | ha x y hx hy =>
      exact (map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
end LittleFinitistic.BimoduleBalancedTensor

end

end OAI
