import OAI.Algebra.AuslanderReiten.Algebras.TrivialExtensionRadical
import OAI.Algebra.AuslanderReiten.Modules.CoinducedBimodule
import OAI.Algebra.AuslanderReiten.Modules.InductionBimodule

namespace OAI

noncomputable section
namespace ArExplicit.TrivialInduction

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]

local notation "T" => TrivialExtension k R

abbrev Middle := InductionBimodule (TrivialExtension.inlHom : R →ₐ[k] T)
abbrev Quotient := InductionBimodule (AlgHom.id k R)

instance dualModule : Module T (Coinduced k R) :=
  Module.compHom (Coinduced k R) TrivialExtension.projection.toRingHom

@[simp] theorem dual_smul (t : T) (φ : Coinduced k R) : t • φ = t.base • φ := rfl

instance : SMulCommClass k T (Coinduced k R) where
  smul_comm a t φ := smul_comm a t.base φ
instance : SMulCommClass T Rᵐᵒᵖ (Coinduced k R) where
  smul_comm t r φ := smul_comm t.base r φ
instance : IsScalarTower k T (Coinduced k R) where
  smul_assoc a t φ := smul_assoc a t.base φ

instance quotientModule : Module T (Quotient (k := k) (R := R)) :=
  Module.compHom _ TrivialExtension.projection.toRingHom

@[simp] theorem quotient_smul_value (t : T) (r : Quotient (k := k) (R := R)) :
    (t • r).value = t.base * r.value := rfl

instance : SMulCommClass k T (Quotient (k := k) (R := R)) where
  smul_comm a t r := smul_comm a t.base r
instance : SMulCommClass T Rᵐᵒᵖ (Quotient (k := k) (R := R)) where
  smul_comm t r s := smul_comm t.base r s
instance : IsScalarTower k T (Quotient (k := k) (R := R)) where
  smul_assoc a t r := smul_assoc a t.base r

def inclusion : Coinduced k R →ₗ[Rᵐᵒᵖ] Middle (k := k) (R := R) where
  toFun φ := ⟨TrivialExtension.inr φ.functional⟩
  map_add' φ ψ := by
    apply InductionBimodule.ext
    apply TrivialExtension.ext
    · exact (zero_add _).symm
    · rfl
  map_smul' r φ := by
    apply InductionBimodule.ext
    apply TrivialExtension.ext
    · exact (zero_mul _).symm
    · ext x
      change φ.functional (r.unop * x) = 0 + φ.functional (r.unop * x)
      exact (zero_add _).symm

def projection : Middle (k := k) (R := R) →ₗ[Rᵐᵒᵖ] Quotient (k := k) (R := R) where
  toFun t := ⟨t.value.base⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem inclusion_value (φ : Coinduced k R) :
    (inclusion φ).value = TrivialExtension.inr φ.functional := rfl
@[simp] theorem projection_value (t : Middle (k := k) (R := R)) :
    (projection t).value = t.value.base := rfl

theorem inclusion_left (t : T) (φ : Coinduced k R) :
    inclusion (t • φ) = t • inclusion φ := by
  apply InductionBimodule.ext
  apply TrivialExtension.ext
  · exact (mul_zero _).symm
  · ext x
    change φ.functional (x * t.base) = φ.functional (x * t.base) + t.dual (0 * x)
    rw [zero_mul, map_zero, add_zero]

theorem projection_left (t : T) (x : Middle (k := k) (R := R)) :
    projection (t • x) = t • projection x := rfl

theorem projection_inclusion :
    (projection (k := k) (R := R)).comp inclusion = 0 := rfl

theorem inclusion_injective : Function.Injective (inclusion (k := k) (R := R)) := by
  intro φ ψ h
  exact Coinduced.ext (congrArg (fun x : Middle (k := k) (R := R) => x.value.dual) h)

theorem projection_surjective : Function.Surjective (projection (k := k) (R := R)) := by
  intro r
  exact ⟨⟨TrivialExtension.inl r.value⟩, rfl⟩

theorem inclusion_projection_exact :
    Function.Exact (inclusion (k := k) (R := R)) projection := by
  intro t
  constructor
  · intro ht
    refine ⟨⟨t.value.dual⟩, ?_⟩
    apply InductionBimodule.ext
    apply TrivialExtension.ext
    · exact (congrArg InductionBimodule.value ht).symm
    · rfl
  · rintro ⟨φ, rfl⟩
    rfl

theorem dual_ideal_annihilates (ψ : Module.Dual k R) (φ : Coinduced k R) :
    TrivialExtension.inr ψ • φ = 0 := by
  change (0 : R) • φ = 0
  exact zero_smul _ _

end ArExplicit.TrivialInduction

end

end OAI
