import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Triangular.Algebra

namespace OAI

section
section
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]
namespace CummingsConstruction
variable {k C ι : Type u} [Field k] [Ring C] [Algebra k C]

abbrev NewCorner (k ι : Type u) := ι → DualNumber k

instance [Finite ι] : FiniteDimensional k (NewCorner k ι) := by
  let : FiniteDimensional k (DualNumber k) := inferInstanceAs (FiniteDimensional k (k × k))
  exact inferInstanceAs (FiniteDimensional k (ι → DualNumber k))

def newAugmentation : NewCorner k ι →ₐ[k] (ι → k) :=
  AlgHom.pi fun i => (TrivSqZeroExt.fstHom k k k).comp (Pi.evalAlgHom k (fun _ : ι => DualNumber k) i)

def SimpleSum (_χ : C →ₐ[k] (ι → k)) := ι → k

namespace SimpleSum
def value {χ : C →ₐ[k] (ι → k)} (x : SimpleSum χ) : ι → k := x
variable (χ : C →ₐ[k] (ι → k))
instance : AddCommGroup (SimpleSum χ) := inferInstanceAs (AddCommGroup (ι → k))
instance : Module k (SimpleSum χ) := inferInstanceAs (Module k (ι → k))
instance [Finite ι] : FiniteDimensional k (SimpleSum χ) := inferInstanceAs (FiniteDimensional k (ι → k))
instance : Module (NewCorner k ι) (SimpleSum χ) :=
  Module.compHom (ι → k) (newAugmentation (k := k) (ι := ι)).toRingHom

def rightCharacter : Cᵐᵒᵖ →+* (ι → k) where
  toFun c := χ c.unop
  map_one' := map_one χ
  map_zero' := map_zero χ
  map_add' x y := map_add χ x.unop y.unop
  map_mul' x y := by simp [map_mul, mul_comm]

instance : Module Cᵐᵒᵖ (SimpleSum χ) := Module.compHom (ι → k) (rightCharacter χ)

instance : SMulCommClass (NewCorner k ι) Cᵐᵒᵖ (SimpleSum χ) where
  smul_comm e c x := by
    change newAugmentation e * (rightCharacter χ c * value x) =
      rightCharacter χ c * (newAugmentation e * value x)
    exact mul_left_comm _ _ _

instance : IsScalarTower k (NewCorner k ι) (SimpleSum χ) where
  smul_assoc r e x := by
    change newAugmentation (r • e) * value x = r • (newAugmentation e * value x)
    rw [map_smul, smul_mul_assoc]

instance : IsScalarTower k Cᵐᵒᵖ (SimpleSum χ) where
  smul_assoc r c x := by
    change χ (r • c.unop) * value x = r • (χ c.unop * value x)
    rw [map_smul, smul_mul_assoc]
end SimpleSum

variable (χ : C →ₐ[k] (ι → k))
abbrev T := TriangularConstruction.Algebra C (NewCorner k ι) (SimpleSum χ)

instance : Algebra k (T χ) := inferInstance
instance [Finite ι] [FiniteDimensional k C] : FiniteDimensional k (T χ) :=
  TriangularConstruction.finiteDimensional C (NewCorner k ι) (SimpleSum χ) k

def augmentation : T χ →ₐ[k] (Sum ι ι → k) where
  toFun x := Sum.elim (χ x.fst.1) (newAugmentation x.fst.2)
  map_one' := by ext i; cases i <;> simp [newAugmentation]
  map_zero' := by ext i; cases i <;> simp [newAugmentation]
  map_add' x y := by ext i; cases i <;> simp [newAugmentation, map_add]
  map_mul' x y := by ext i; cases i <;> simp [newAugmentation, map_mul]
  commutes' r := by ext i; cases i <;> simp [newAugmentation, Algebra.algebraMap_eq_smul_one]

lemma augmentation_surjective (hχ : Function.Surjective χ) : Function.Surjective (augmentation χ) := by
  intro v
  obtain ⟨c, hc⟩ := hχ (v ∘ Sum.inl)
  refine ⟨((c, fun i => TrivSqZeroExt.inl (v (.inr i))), 0), ?_⟩
  ext i
  cases i with
  | inl i => exact congrFun hc i
  | inr i => rfl

variable [DecidableEq ι]

def socle : Sum ι ι → T χ
  | .inl i => (0, Pi.single i 1)
  | .inr i => ((0, Pi.single i DualNumber.eps), 0)

lemma socle_ne_zero (i : Sum ι ι) : socle χ i ≠ 0 := by
  intro h
  cases i with
  | inl i =>
    have := congrArg (fun x : T χ => (TriangularConstruction.offValue x.snd : ι → k) i) h
    change (Pi.single i (1 : k) : ι → k) i = 0 at this
    simp at this
  | inr i =>
    have := congrArg (fun x : T χ => (x.fst.2 i).snd) h
    simp [socle] at this

lemma socle_mul (i : Sum ι ι) (x : T χ) :
    socle χ i * x = augmentation χ x i • socle χ i := by
  cases i with
  | inl i =>
    apply TrivSqZeroExt.ext
    · change (0 : C × NewCorner k ι) * x.fst = _ • 0
      simp
    · change newAugmentation (0 : NewCorner k ι) * (SimpleSum.value (TriangularConstruction.offValue x.snd)) +
        SimpleSum.rightCharacter χ (MulOpposite.op x.fst.1) * (Pi.single i 1 : ι → k) =
        χ x.fst.1 i • (Pi.single i 1 : ι → k)
      ext j
      by_cases h : j = i
      · subst j; simp [SimpleSum.rightCharacter]
      · simp [h]
  | inr i =>
    apply TrivSqZeroExt.ext
    · apply Prod.ext
      · change (0 : C) * x.fst.1 = _ • 0
        simp
      · change (Pi.single i DualNumber.eps : ι → DualNumber k) * x.fst.2 =
          (x.fst.2 i).fst • (Pi.single i DualNumber.eps : ι → DualNumber k)
        ext j : 1
        by_cases h : j = i
        · subst j
          simp only [Pi.mul_apply, Pi.smul_apply, Pi.single_eq_same]
          apply TrivSqZeroExt.ext <;> simp
        · simp [h]
    · apply funext
      intro j
      change (newAugmentation (Pi.single i (DualNumber.eps : DualNumber k))) j *
        (SimpleSum.value (TriangularConstruction.offValue x.snd)) j + χ x.fst.1 j * 0 =
        (x.fst.2 i).fst * 0
      have he : newAugmentation (Pi.single i (DualNumber.eps : DualNumber k)) = (0 : ι → k) := by
        ext j
        by_cases h : j = i
        · subst j; simp [newAugmentation]
        · simp [newAugmentation, h]
      simp [he]

end CummingsConstruction
end LittleFinitistic
end
end
end

end OAI
