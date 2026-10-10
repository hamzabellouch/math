import OAI.Algebra.AuslanderReiten.Modules.CoinducedBimodule
import Mathlib.Algebra.Module.Opposite

namespace OAI

noncomputable section
namespace ArExplicit

@[ext] structure RightDual (k R V : Type*) [CommRing k] [Ring R]
    [AddCommGroup V] [Module k V] [Module Rᵐᵒᵖ V] where
  functional : Module.Dual k V

namespace RightDual
variable {k R V W U : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup V] [Module k V] [Module Rᵐᵒᵖ V] [IsScalarTower k Rᵐᵒᵖ V]
variable [AddCommGroup W] [Module k W] [Module Rᵐᵒᵖ W] [IsScalarTower k Rᵐᵒᵖ W]
variable [AddCommGroup U] [Module k U] [Module Rᵐᵒᵖ U] [IsScalarTower k Rᵐᵒᵖ U]

def coordinates : RightDual k R V ≃ Module.Dual k V where
  toFun := functional
  invFun := RightDual.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (RightDual k R V) := coordinates.addCommGroup
instance : Module k (RightDual k R V) := coordinates.addEquiv.module k

omit [Algebra k R] [IsScalarTower k Rᵐᵒᵖ V] in
@[simp] theorem functional_zero : (0 : RightDual k R V).functional = 0 := rfl
omit [Algebra k R] [IsScalarTower k Rᵐᵒᵖ V] in
@[simp] theorem functional_add (φ ψ : RightDual k R V) :
    (φ + ψ).functional = φ.functional + ψ.functional := rfl
omit [Algebra k R] [IsScalarTower k Rᵐᵒᵖ V] in
@[simp] theorem functional_smul (a : k) (φ : RightDual k R V) :
    (a • φ).functional = a • φ.functional := rfl

def scalarEquiv : RightDual k R V ≃ₗ[k] Module.Dual k V :=
  coordinates.addEquiv.linearEquiv k

instance : SMul R (RightDual k R V) :=
  ⟨fun r φ => ⟨{
    toFun := fun v => φ.functional (MulOpposite.op r • v)
    map_add' := fun v w => by simp
    map_smul' := fun a v => by simp [smul_comm (MulOpposite.op r) a v] }⟩⟩

@[simp] theorem functional_action (r : R) (φ : RightDual k R V) (v : V) :
    (r • φ).functional v = φ.functional (MulOpposite.op r • v) := rfl

instance : Module R (RightDual k R V) where
  one_smul φ := by ext v; simp
  mul_smul r s φ := by ext v; simp [MulOpposite.op_mul, mul_smul]
  smul_zero r := by ext v; simp
  smul_add r φ ψ := by ext v; simp
  zero_smul φ := by ext v; simp
  add_smul r s φ := by ext v; simp [add_smul]

instance : IsScalarTower k R (RightDual k R V) where
  smul_assoc a r φ := by ext v; simp [MulOpposite.op_smul, smul_assoc]
instance : SMulCommClass k R (RightDual k R V) where
  smul_comm a r φ := by ext v; rfl

def map (f : V →ₗ[Rᵐᵒᵖ] W) : RightDual k R W →ₗ[R] RightDual k R V where
  toFun φ := ⟨φ.functional.comp (f.restrictScalars k)⟩
  map_add' φ ψ := by ext v; rfl
  map_smul' r φ := by ext v; simp

@[simp] theorem map_apply (f : V →ₗ[Rᵐᵒᵖ] W) (φ : RightDual k R W) (v : V) :
    (map f φ).functional v = φ.functional (f v) := rfl

theorem map_comp (f : U →ₗ[Rᵐᵒᵖ] V) (g : V →ₗ[Rᵐᵒᵖ] W) :
    map (k := k) (g.comp f) = (map f).comp (map g) := rfl

def congr (e : V ≃ₗ[Rᵐᵒᵖ] W) : RightDual k R W ≃ₗ[R] RightDual k R V where
  __ := map e.toLinearMap
  invFun := map e.symm.toLinearMap
  left_inv φ := by ext w; simp
  right_inv φ := by ext v; simp

end RightDual

namespace RightDual
variable {k R U V W : Type*} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup U] [Module k U] [Module Rᵐᵒᵖ U] [IsScalarTower k Rᵐᵒᵖ U]
variable [AddCommGroup V] [Module k V] [Module Rᵐᵒᵖ V] [IsScalarTower k Rᵐᵒᵖ V]
variable [AddCommGroup W] [Module k W] [Module Rᵐᵒᵖ W] [IsScalarTower k Rᵐᵒᵖ W]

theorem map_exact (f : U →ₗ[Rᵐᵒᵖ] V) (g : V →ₗ[Rᵐᵒᵖ] W) (h : Function.Exact f g) :
    Function.Exact (map (k := k) g) (map f) := by
  intro φ
  constructor
  · intro hφ
    have ha : φ.functional ∈ (LinearMap.ker (g.restrictScalars k)).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro v hv
      obtain ⟨u, rfl⟩ := (h v).mp hv
      exact congrArg (fun ψ : RightDual k R U => ψ.functional u) hφ
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at ha
    obtain ⟨ψ, hψ⟩ := ha
    exact ⟨⟨ψ⟩, RightDual.ext hψ⟩
  · rintro ⟨ψ, rfl⟩
    ext u
    change ψ.functional (g (f u)) = 0
    rw [(h (f u)).mpr ⟨u, rfl⟩, map_zero]

theorem map_surjective (f : U →ₗ[Rᵐᵒᵖ] V) (hf : Function.Injective f) :
    Function.Surjective (map (k := k) f) := by
  intro φ
  obtain ⟨ψ, hψ⟩ := LinearMap.dualMap_surjective_of_injective
    (f := f.restrictScalars k) hf φ.functional
  exact ⟨⟨ψ⟩, RightDual.ext hψ⟩

end RightDual
end ArExplicit

end

end OAI
