import Mathlib
import OAI.Algebra.FinitisticAsymmetry.ZeroDimensions
import OAI.Algebra.FinitisticAsymmetry.Triangular.Socle

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
variable (χ : C →ₐ[k] (ι → k))
lemma mem_ker_augmentation (x : T χ) :
    x ∈ RingHom.ker (augmentation χ).toRingHom ↔ χ x.fst.1 = 0 ∧ newAugmentation x.fst.2 = 0 := by
  change (Sum.elim (χ x.fst.1) (newAugmentation x.fst.2) : Sum ι ι → k) = 0 ↔ _
  constructor
  · intro h
    exact ⟨funext fun i => congrFun h (.inl i), funext fun i => congrFun h (.inr i)⟩
  · rintro ⟨h₁, h₂⟩
    ext i
    cases i <;> simp [h₁, h₂]

def pureOldRadical : Ideal (T χ) where
  carrier := {x | x.fst.2 = 0 ∧ (SimpleSum.value (TriangularConstruction.offValue x.snd)) = 0 ∧ χ x.fst.1 = 0}
  zero_mem' := ⟨rfl, rfl, map_zero χ⟩
  add_mem' := by
    rintro x y ⟨hxe, hxu, hxc⟩ ⟨hye, hyu, hyc⟩
    change x.fst.2 + y.fst.2 = 0 ∧
      SimpleSum.value (TriangularConstruction.offValue x.snd) + SimpleSum.value (TriangularConstruction.offValue y.snd) = 0 ∧ χ (x.fst.1 + y.fst.1) = 0
    simp [hxe, hye, hxu, hyu, hxc, hyc, map_add]
  smul_mem' := by
    rintro r x ⟨hxe, hxu, hxc⟩
    change r.fst.2 * x.fst.2 = 0 ∧
      newAugmentation r.fst.2 * SimpleSum.value (TriangularConstruction.offValue x.snd) +
        χ x.fst.1 * SimpleSum.value (TriangularConstruction.offValue r.snd) = 0 ∧ χ (r.fst.1 * x.fst.1) = 0
    simp [hxe, hxu, hxc, map_mul]

lemma ker_square_pureOldRadical :
    (RingHom.ker (augmentation χ).toRingHom) ^ 2 ≤ pureOldRadical χ := by
  rw [Submodule.pow_succ, Submodule.pow_one]
  apply Ideal.mul_le.mpr
  intro x hx y hy
  obtain ⟨hxc, hxe⟩ := (mem_ker_augmentation χ x).mp hx
  obtain ⟨hyc, hye⟩ := (mem_ker_augmentation χ y).mp hy
  change x.fst.2 * y.fst.2 = 0 ∧
    newAugmentation x.fst.2 * SimpleSum.value (TriangularConstruction.offValue y.snd) +
      χ y.fst.1 * SimpleSum.value (TriangularConstruction.offValue x.snd) = 0 ∧ χ (x.fst.1 * y.fst.1) = 0
  refine ⟨?_, by simp [hxe, hyc], by simp [map_mul, hxc]⟩
  ext i : 1
  have hx0 : (x.fst.2 i).fst = 0 := congrFun hxe i
  have hy0 : (y.fst.2 i).fst = 0 := congrFun hye i
  apply TrivSqZeroExt.ext <;> simp [hx0, hy0]

lemma pow_le_comap_pow_noncomm {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (I : Ideal R) (J : Ideal S) (h : I ≤ J.comap f) (n : ℕ) : I ^ n ≤ (J ^ n).comap f := by
  induction n with
  | zero => simp [Submodule.pow_zero, Ideal.one_eq_top]
  | succ n ih =>
    rw [Submodule.pow_succ, Submodule.pow_succ]
    apply Ideal.mul_le.mpr
    intro x hx y hy
    change f (x * y) ∈ J ^ n * J
    rw [map_mul]
    exact Ideal.mul_mem_mul (ih hx) (h hy)

lemma augmentation_ker_nilpotent (hJ : ∃ n : ℕ, (RingHom.ker χ.toRingHom) ^ n = ⊥) :
    ∃ n : ℕ, (RingHom.ker (augmentation χ).toRingHom) ^ n = ⊥ := by
  obtain ⟨n, hn⟩ := hJ
  let K := RingHom.ker (augmentation χ).toRingHom
  let J := RingHom.ker χ.toRingHom
  have hcomap : K ≤ J.comap (TriangularConstruction.toC C (NewCorner k ι) (SimpleSum χ)) := by
    intro x hx
    exact ((mem_ker_augmentation χ x).mp hx).1
  have hpow := pow_le_comap_pow_noncomm _ K J hcomap (n + 2)
  have hjn : J ^ (n + 2) = ⊥ := by
    apply le_bot_iff.mp
    exact (Ideal.pow_le_pow_right (I := J) (Nat.le_add_right n 2)).trans hn.le
  rw [hjn] at hpow
  refine ⟨n + 2, le_bot_iff.mp ?_⟩
  intro x hx
  have hc : x.fst.1 = 0 := hpow hx
  have hp := ker_square_pureOldRadical χ ((Ideal.pow_le_pow_right (I := K) (by omega : 2 ≤ n + 2)) hx)
  change x = 0
  apply TrivSqZeroExt.ext
  · exact Prod.ext hc hp.1
  · exact hp.2.1

variable [DecidableEq ι]

lemma left_dimensions_zero [Finite ι] [Nontrivial C]
    (hχ : Function.Surjective χ) (hJ : ∃ n : ℕ, (RingHom.ker χ.toRingHom) ^ n = ⊥) :
    littleFinitisticDimension (T χ) = 0 ∧ bigFinitisticDimension (T χ) = 0 := by
  let : Nontrivial (T χ) := inferInstanceAs (Nontrivial ((C × NewCorner k ι) ×
    TriangularConstruction.OffDiagonal C (NewCorner k ι) (SimpleSum χ)))
  exact dimensions_zero_of_splitBasic_rightSocle (augmentation χ)
    (augmentation_surjective χ hχ) (augmentation_ker_nilpotent χ hJ)
    (socle χ) (socle_ne_zero χ) (socle_mul χ)

end CummingsConstruction
end LittleFinitistic

end
end
end

end OAI
