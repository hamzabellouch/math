import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace OAI
open scoped TensorProduct


noncomputable section
namespace ExternalTensor

variable (k B M N : Type*) [Field k] [Ring B] [Algebra k B]
  [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M]
  [AddCommGroup N] [Module k N] [Module Bᵐᵒᵖ N] [IsScalarTower k Bᵐᵒᵖ N]

def leftAction : B →ₐ[k] Module.End k (M ⊗[k] N) :=
  (Module.End.rTensorAlgHom k M N).comp (Algebra.lsmul k k M)

def rightAction : Bᵐᵒᵖ →ₐ[k] Module.End k (M ⊗[k] N) :=
  (Module.End.lTensorAlgHom k N M).comp (Algebra.lsmul k k N)

omit [Module Bᵐᵒᵖ N] [IsScalarTower k Bᵐᵒᵖ N] in
@[simp] theorem leftAction_tmul (b : B) (m : M) (n : N) :
    leftAction k B M N b (m ⊗ₜ[k] n) = (b • m) ⊗ₜ[k] n := rfl

omit [Module B M] [IsScalarTower k B M] in
@[simp] theorem rightAction_tmul (b : Bᵐᵒᵖ) (m : M) (n : N) :
    rightAction k B M N b (m ⊗ₜ[k] n) = m ⊗ₜ[k] (b • n) := rfl

theorem actions_commute (b : B) (c : Bᵐᵒᵖ) :
    Commute (leftAction k B M N b) (rightAction k B M N c) := by
  apply TensorProduct.ext
  ext m n
  rfl

/-- The genuine enveloping algebra representation; the right action is encoded by Bᵐᵒᵖ. -/
def action : (B ⊗[k] Bᵐᵒᵖ) →ₐ[k] Module.End k (M ⊗[k] N) :=
  Algebra.TensorProduct.lift (leftAction k B M N) (rightAction k B M N)
    (actions_commute k B M N)

@[instance_reducible] def bimodule : Module (B ⊗[k] Bᵐᵒᵖ) (M ⊗[k] N) :=
  Module.compHom (M ⊗[k] N) (action k B M N).toRingHom

@[instance_reducible] def rightModule : Module Bᵐᵒᵖ (M ⊗[k] N) :=
  Module.compHom (M ⊗[k] N) (rightAction k B M N).toRingHom

attribute [local instance] bimodule rightModule

@[simp] theorem smul_tmul (b : B) (c : Bᵐᵒᵖ) (m : M) (n : N) :
    (b ⊗ₜ[k] c) • (m ⊗ₜ[k] n) = (b • m) ⊗ₜ[k] (c • n) := rfl

omit [Module B M] [IsScalarTower k B M] in
@[simp] theorem right_smul_tmul (c : Bᵐᵒᵖ) (m : M) (n : N) :
    c • (m ⊗ₜ[k] n) = m ⊗ₜ[k] (c • n) := rfl


/-- Factor swap, with the external right action on the source. -/
def rightSwap : (M ⊗[k] N) ≃ₗ[Bᵐᵒᵖ] (N ⊗[k] M) where
  __ := (TensorProduct.comm k M N).toAddEquiv
  map_smul' c x := by
    induction x using TensorProduct.inductionOn with
    | tmul m n => simp [right_smul_tmul, TensorProduct.smul_tmul']
    | add x y hx hy => simp_all [smul_add]

omit [Module B M] [IsScalarTower k B M] in
/-- In fact no dimension restriction on M is needed for right projectivity. -/
theorem projective_right [Module.Projective Bᵐᵒᵖ N] :
    Module.Projective Bᵐᵒᵖ (M ⊗[k] N) :=
  Module.Projective.of_equiv (rightSwap k B M N).symm

theorem finiteDimensional [FiniteDimensional k M] [FiniteDimensional k N] :
    FiniteDimensional k (M ⊗[k] N) :=
  Module.Finite.equiv
    (TensorProduct.equivFinsuppOfBasisLeft (Module.finBasis k M)).symm


/-- A k-basis of the left factor gives an actual right-module direct-sum decomposition. -/
def rightBasisEquiv {ι : Type*} [DecidableEq ι] (v : Module.Basis ι k M) :
    (M ⊗[k] N) ≃ₗ[Bᵐᵒᵖ] (ι →₀ N) where
  __ := (TensorProduct.equivFinsuppOfBasisLeft v).toAddEquiv
  map_smul' c x := by
    induction x using TensorProduct.inductionOn with
    | tmul m n =>
      ext i
      change (TensorProduct.equivFinsuppOfBasisLeft v)
        (c • (m ⊗ₜ[k] n)) i = c • (TensorProduct.equivFinsuppOfBasisLeft v) (m ⊗ₜ[k] n) i
      rw [right_smul_tmul, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
      exact smul_comm (v.repr m i) c n
    | add x y hx hy => simp_all [smul_add]

omit [Module B M] [IsScalarTower k B M] in
@[simp] theorem rightBasisEquiv_tmul {ι : Type*} [DecidableEq ι]
    (v : Module.Basis ι k M) (m : M) (n : N) (i : ι) :
    rightBasisEquiv k B M N v (m ⊗ₜ[k] n) i = v.repr m i • n :=
  TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply v m n i

omit [Module B M] [IsScalarTower k B M] in
theorem finite_right [FiniteDimensional k M] [Module.Finite Bᵐᵒᵖ N] :
    Module.Finite Bᵐᵒᵖ (M ⊗[k] N) :=
  Module.Finite.equiv (rightBasisEquiv k B M N (Module.finBasis k M)).symm


/-- The chosen right action is the restriction of the enveloping action. -/
theorem right_eq_enveloping (c : Bᵐᵒᵖ) (x : M ⊗[k] N) :
    c • x = (1 ⊗ₜ[k] c : B ⊗[k] Bᵐᵒᵖ) • x := by
  induction x using TensorProduct.inductionOn with
  | tmul m n => simp
  | add x y hx hy => simp_all [smul_add]

/-- The usual left action on the first tensor factor is the other restriction. -/
theorem left_eq_enveloping (b : B) (x : M ⊗[k] N) :
    b • x = (b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • x := by
  induction x using TensorProduct.inductionOn with
  | tmul m n => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp_all [smul_add]

instance commutingActions : SMulCommClass B Bᵐᵒᵖ (M ⊗[k] N) where
  smul_comm b c x := by
    induction x using TensorProduct.inductionOn with
    | tmul m n => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp_all [smul_add]

instance rightScalarTower : IsScalarTower k Bᵐᵒᵖ (M ⊗[k] N) where
  smul_assoc r c x := by
    change rightAction k B M N (r • c) x = r • rightAction k B M N c x
    rw [map_smul]
    rfl

instance envelopingScalarTower : IsScalarTower k (B ⊗[k] Bᵐᵒᵖ) (M ⊗[k] N) where
  smul_assoc r a x := by
    change action k B M N (r • a) x = r • action k B M N a x
    rw [map_smul]
    rfl

variable {k B M N}
variable {M' N' : Type*}
  [AddCommGroup M'] [Module k M'] [Module B M'] [IsScalarTower k B M']
  [AddCommGroup N'] [Module k N'] [Module Bᵐᵒᵖ N'] [IsScalarTower k Bᵐᵒᵖ N']

/-- Tensor of a left-module map and a right-module map is enveloping-linear. -/
def map (f : M →ₗ[B] M') (g : N →ₗ[Bᵐᵒᵖ] N') :
    (M ⊗[k] N) →ₗ[B ⊗[k] Bᵐᵒᵖ] (M' ⊗[k] N') where
  __ := (TensorProduct.map (f.restrictScalars k) (g.restrictScalars k)).toAddMonoidHom
  map_smul' a x := by
    induction a using TensorProduct.inductionOn with
    | tmul b c =>
      induction x using TensorProduct.inductionOn with
      | tmul m n => simp [smul_tmul]
      | add x y hx hy => simp_all [smul_add]
    | add a b ha hb => simp_all [add_smul]

@[simp] theorem map_tmul (f : M →ₗ[B] M') (g : N →ₗ[Bᵐᵒᵖ] N') (m : M) (n : N) :
    map (k := k) f g (m ⊗ₜ[k] n) = f m ⊗ₜ[k] g n := rfl

@[simp] theorem map_id :
    map (k := k) (LinearMap.id : M →ₗ[B] M) (LinearMap.id : N →ₗ[Bᵐᵒᵖ] N) =
      LinearMap.id := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul m n => rfl
  | add x y hx hy => simp_all

variable {M'' N'' : Type*}
  [AddCommGroup M''] [Module k M''] [Module B M''] [IsScalarTower k B M'']
  [AddCommGroup N''] [Module k N''] [Module Bᵐᵒᵖ N''] [IsScalarTower k Bᵐᵒᵖ N'']

theorem map_comp (f : M →ₗ[B] M') (f' : M' →ₗ[B] M'')
    (g : N →ₗ[Bᵐᵒᵖ] N') (g' : N' →ₗ[Bᵐᵒᵖ] N'') :
    map (k := k) (f'.comp f) (g'.comp g) = (map (k := k) f' g').comp (map (k := k) f g) := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul m n => rfl
  | add x y hx hy => simp_all


theorem map_add_left (f f' : M →ₗ[B] M') (g : N →ₗ[Bᵐᵒᵖ] N') :
    map (k := k) (f + f') g = map (k := k) f g + map (k := k) f' g := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul m n => simp [TensorProduct.add_tmul]
  | add x y hx hy => simp_all [add_add_add_comm]

theorem map_add_right (f : M →ₗ[B] M') (g g' : N →ₗ[Bᵐᵒᵖ] N') :
    map (k := k) f (g + g') = map (k := k) f g + map (k := k) f g' := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul m n => simp [TensorProduct.tmul_add]
  | add x y hx hy => simp_all [add_add_add_comm]


theorem map_smul_left (r : k) (f : M →ₗ[B] M') (g : N →ₗ[Bᵐᵒᵖ] N') :
    map (k := k) (r • f) g = r • map (k := k) f g := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul m n => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp_all [smul_add]

theorem map_smul_right (r : k) (f : M →ₗ[B] M') (g : N →ₗ[Bᵐᵒᵖ] N') :
    map (k := k) f (r • g) = r • map (k := k) f g := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul m n => simp [TensorProduct.tmul_smul]
  | add x y hx hy => simp_all [smul_add]

/-- The same tensor map as a map of right B-modules. -/
def rightMap (f : M →ₗ[B] M') (g : N →ₗ[Bᵐᵒᵖ] N') :
    (M ⊗[k] N) →ₗ[Bᵐᵒᵖ] (M' ⊗[k] N') where
  __ := (map (k := k) f g).toAddMonoidHom
  map_smul' c x := by
    change map (k := k) f g (c • x) = c • map (k := k) f g x
    rw [right_eq_enveloping, right_eq_enveloping, LinearMap.map_smul]

@[simp] theorem rightMap_tmul (f : M →ₗ[B] M') (g : N →ₗ[Bᵐᵒᵖ] N') (m : M) (n : N) :
    rightMap (k := k) f g (m ⊗ₜ[k] n) = f m ⊗ₜ[k] g n := rfl
end ExternalTensor

end

end OAI
