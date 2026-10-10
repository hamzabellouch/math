import Mathlib.Algebra.Algebra.Hom
import OAI.Algebra.Finitistic.Localization.OddDouble

namespace OAI

open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive
open CategoryTheory.Idempotents CategoryTheory.Limits

namespace LittleFinitistic.FormalSummandAction

universe u v w
variable {k : Type w} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

instance karoubiHomSMul (P Q : Karoubi C) : SMul k (P ⟶ Q) where
  smul r f := ⟨r • f.f, by rw [Linear.smul_comp,Linear.comp_smul,f.comm]⟩

@[simp] theorem smul_f (P Q : Karoubi C) (r : k) (f : P ⟶ Q) :
    (r • f).f = r • f.f := rfl

instance karoubiHomModule (P Q : Karoubi C) : Module k (P ⟶ Q) :=
  Function.Injective.module k (Karoubi.inclusionHom P Q)
    (fun _ _ h => Karoubi.hom_ext _ _ h) (fun _ _ => rfl)

instance karoubiLinear : Linear k (Karoubi C) where
  smul_comp _ _ _ _ _ _ := by apply Karoubi.hom_ext; exact Linear.smul_comp _ _ _ _ _ _
  comp_smul _ _ _ _ _ _ := by apply Karoubi.hom_ext; exact Linear.comp_smul _ _ _ _ _ _

instance toKaroubiLinear : (toKaroubi C).Linear k where
  map_smul := by intros; rfl

variable {R : Type*} [Ring R] [Algebra k R]
variable {L : C} (θ : R →ₐ[k] End L) (e : R) (he : e * e = e)

/-- The formal image of the central selecting idempotent. -/
def summand : Karoubi C :=
  ⟨L,θ e,by change θ e * θ e = θ e; rw [← map_mul,he]⟩

variable (hc : ∀ r : R, e * r = r * e)

include he hc in
lemma sandwich (r : R) : e * r * e = e * r := by
  calc
    e * r * e = e * e * r := by rw [mul_assoc,← hc r,← mul_assoc]
    _ = e * r := by rw [he]

include he hc in
lemma compressed_mul (r s : R) : (e*r)*(e*s) = e*(r*s) := by
  rw [← mul_assoc,sandwich e he hc,mul_assoc]

/-- The action on the formal summand, with restriction along alpha. -/
def action (α : R →ₐ[k] R) : R →ₐ[k] End (summand θ e he) where
  toFun r := ⟨θ (e * α r),by
    change θ e ≫ θ (e * α r) ≫ θ e = θ (e * α r)
    change (θ e * θ (e * α r)) * θ e = θ (e * α r)
    rw [← map_mul,← map_mul]
    congr 1
    rw [← mul_assoc e e,he,sandwich e he hc]⟩
  map_one' := by apply Karoubi.hom_ext; change θ (e * α 1) = θ e; rw [map_one,mul_one]
  map_mul' r s := by
    apply Karoubi.hom_ext
    change θ (e * α (r*s)) = θ (e * α r) * θ (e * α s)
    rw [← map_mul θ,map_mul α,compressed_mul e he hc]
  map_zero' := by apply Karoubi.hom_ext; change θ (e * α 0) = 0; simp
  map_add' r s := by apply Karoubi.hom_ext; change θ (e * α (r+s)) = θ (e * α r) + θ (e * α s); simp [mul_add]
  commutes' r := by
    apply Karoubi.hom_ext
    change θ (e * α (algebraMap k R r)) = (algebraMap k (End (summand θ e he)) r).f
    rw [α.commutes]
    change θ (e * algebraMap k R r) = (r • (𝟙 (summand θ e he))).f
    rw [smul_f]
    change θ (e * algebraMap k R r) = r • θ e
    rw [hc,Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul,map_smul]

@[simp] theorem action_f (α : R →ₐ[k] R) (r : R) :
    ((action θ e he hc α r) : End (summand θ e he)).f = θ (e * α r * e) := by
  rw [sandwich e he hc]
  rfl

variable {D : Type*} [Category D] [Preadditive D] [Linear k D]

/-- A linear functor transports an algebra action on endomorphisms. -/
def mapAction (F : C ⥤ D) [F.Additive] [F.Linear k] {X : C}
    (ρ : R →ₐ[k] End X) : R →ₐ[k] End (F.obj X) where
  toFun r := F.map (ρ r)
  map_one' := by simp
  map_mul' r s := by simp [End.mul_def]
  map_zero' := by simp
  map_add' r s := by rw [map_add]; exact F.map_add
  commutes' r := by
    rw [ρ.commutes]
    change F.map (r • (𝟙 X)) = r • (𝟙 (F.obj X))
    rw [Functor.map_smul,F.map_id]

/-- Direct sum of two actions of the same algebra. -/
noncomputable def biprodAction [HasBinaryBiproducts C] {X Y : C}
    (ρ : R →ₐ[k] End X) (σ : R →ₐ[k] End Y) : R →ₐ[k] End (X ⊞ Y) where
  toFun r := biprod.map (ρ r) (σ r)
  map_one' := by apply biprod.hom_ext <;> simp
  map_mul' r s := by apply biprod.hom_ext <;> simp [End.mul_def]
  map_zero' := by apply biprod.hom_ext <;> simp
  map_add' r s := by
    rw [map_add,map_add]
    change biprod.map ((ρ r : X ⟶ X) + (ρ s : X ⟶ X))
      ((σ r : Y ⟶ Y) + (σ s : Y ⟶ Y)) =
      (biprod.map (ρ r) (σ r) : X ⊞ Y ⟶ X ⊞ Y) + biprod.map (ρ s) (σ s)
    apply biprod.hom_ext <;> simp only [biprod.map_fst,biprod.map_snd,
      Preadditive.add_comp]
    all_goals exact Preadditive.comp_add _ _ _ _ _ _
  commutes' r := by
    rw [ρ.commutes,σ.commutes]
    change biprod.map (r • (𝟙 X)) (r • (𝟙 Y)) = r • (𝟙 (X ⊞ Y))
    apply biprod.hom_ext <;> simp

/-- Conjugating an action along an isomorphism. -/
def transportAction {X Y : C} (i : X ≅ Y) (ρ : R →ₐ[k] End Y) :
    R →ₐ[k] End X where
  toFun r := i.hom ≫ ρ r ≫ i.inv
  map_one' := by simp
  map_mul' r s := by simp [End.mul_def]
  map_zero' := by simp
  map_add' r s := by
    rw [map_add]
    change i.hom ≫ ((ρ r : Y ⟶ Y) + (ρ s : Y ⟶ Y)) ≫ i.inv = _
    rw [add_comp,comp_add]
  commutes' r := by
    rw [ρ.commutes]
    change i.hom ≫ (r • (𝟙 Y)) ≫ i.inv = r • (𝟙 X)
    simp

/-- An action on an old object in the completion is an actual old action. -/
def oldAction {X : C} (ρ : R →ₐ[k] End ((toKaroubi C).obj X)) :
    R →ₐ[k] End X where
  toFun r := (ρ r).f
  map_one' := by rw [map_one]; rfl
  map_mul' r s := by rw [map_mul]; rfl
  map_zero' := by rw [map_zero]; rfl
  map_add' r s := by rw [map_add]; rfl
  commutes' r := by rw [ρ.commutes]; rfl

@[simp] theorem oldAction_lift {X : C} (ρ : R →ₐ[k] End ((toKaroubi C).obj X))
    (r : R) : (toKaroubi C).map (oldAction ρ r) = ρ r := by
  apply Karoubi.hom_ext
  rfl

variable [HasShift C ℤ] [HasZeroObject C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [∀ n : ℤ, (shiftFunctor C n).Linear k]

instance formalShiftLinear (n : ℤ) :
    (OddDouble.formalShiftFunctor (C := C) n).Linear k where
  map_smul := by
    intro X Y f r
    apply Karoubi.hom_ext
    exact Functor.map_smul (shiftFunctor C n) r f.f

local instance : HasFiniteBiproducts (Karoubi C) := Karoubi.karoubi_hasFiniteBiproducts
local instance : HasBinaryBiproducts (Karoubi C) :=
  hasBinaryBiproducts_of_finite_biproducts (Karoubi C)

/-- The selecting action on the odd double. -/
noncomputable def oddDoubleAction (α : R →ₐ[k] R) :
    R →ₐ[k] End (summand θ e he ⊞ OddDouble.formalShift (summand θ e he) 3) :=
  biprodAction (action θ e he hc α)
    (mapAction (OddDouble.formalShiftFunctor 3) (action θ e he hc α))

/-- The object and its unital action are both chosen before any evaluation module. -/
theorem fixed_old_object_with_action (α : R →ₐ[k] R) :
    ∃ (V₀ : C) (ρ₀ : R →ₐ[k] End V₀)
      (i : (toKaroubi C).obj V₀ ≅
        summand θ e he ⊞ OddDouble.formalShift (summand θ e he) 3),
      ∀ r : R, (toKaroubi C).map (ρ₀ r) ≫ i.hom =
        i.hom ≫ oddDoubleAction θ e he hc α r := by
  obtain ⟨V₀,⟨i⟩⟩ := OddDouble.odd_double_three (summand θ e he)
  let σ := oddDoubleAction θ e he hc α
  let τ := transportAction i σ
  refine ⟨V₀,oldAction τ,i,?_⟩
  intro r
  rw [oldAction_lift]
  change (i.hom ≫ σ r ≫ i.inv) ≫ i.hom = i.hom ≫ σ r
  simp

end LittleFinitistic.FormalSummandAction

end OAI
