import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Model

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace LittleFinitistic.SplitBasic
universe v
variable {k : Type v} [Field k]
lemma pow_le_comap_pow {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
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

section SquareZero
variable {R M : Type v} [Ring R] [Algebra k R] [AddCommGroup M]
  [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
  [Module k M] [IsScalarTower k R M] [IsScalarTower k Rᵐᵒᵖ M]
variable {ι : Type v} (χ : R →ₐ[k] (ι → k))
def squareZeroAugmentation : TrivSqZeroExt R M →ₐ[k] (ι → k) :=
  χ.comp (TrivSqZeroExt.fstHom k R M)
lemma squareZero_surjective (hχ : Function.Surjective χ) :
    Function.Surjective (squareZeroAugmentation (M := M) χ) := by
  intro s
  obtain ⟨r, hr⟩ := hχ s
  exact ⟨TrivSqZeroExt.inl r, hr⟩
lemma squareZero_ker_nilpotent (hJ : ∃ n : ℕ, (RingHom.ker χ.toRingHom) ^ n = ⊥) :
    ∃ n : ℕ, (RingHom.ker (squareZeroAugmentation (M := M) χ).toRingHom) ^ n = ⊥ := by
  obtain ⟨n, hn⟩ := hJ
  let f := (TrivSqZeroExt.fstHom k R M).toRingHom
  let K := RingHom.ker (squareZeroAugmentation (M := M) χ).toRingHom
  let J := RingHom.ker χ.toRingHom
  let L := RingHom.ker f
  have h : K ^ n ≤ L := by
    have hp := pow_le_comap_pow f K J (by intro x hx; exact hx) n
    rw [hn] at hp
    exact hp
  have hL : L * L = ⊥ := by
    apply le_bot_iff.mp
    apply Ideal.mul_le.mpr
    intro x hx y hy
    change x.fst = 0 at hx
    change y.fst = 0 at hy
    change x * y = 0
    apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, hx, hy]
  refine ⟨n + n, le_bot_iff.mp ?_⟩
  rw [Ideal.IsTwoSided.pow_add]
  exact (Ideal.mul_mono h h).trans hL.le
end SquareZero

section Product
variable {R S ι κ : Type v} [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable (χ : R →ₐ[k] (ι → k)) (ψ : S →ₐ[k] (κ → k))
def productAugmentation : R × S →ₐ[k] (Sum ι κ → k) where
  toFun x := Sum.elim (χ x.1) (ψ x.2)
  map_one' := by ext i; cases i <;> simp
  map_zero' := by ext i; cases i <;> simp
  map_add' x y := by ext i; cases i <;> simp
  map_mul' x y := by ext i; cases i <;> simp
  commutes' r := by ext i; cases i <;> simp
lemma product_surjective (hχ : Function.Surjective χ) (hψ : Function.Surjective ψ) :
    Function.Surjective (productAugmentation χ ψ) := by
  intro s
  obtain ⟨r, hr⟩ := hχ (s ∘ Sum.inl)
  obtain ⟨t, ht⟩ := hψ (s ∘ Sum.inr)
  refine ⟨(r,t), ?_⟩
  ext i
  cases i <;> simp [productAugmentation, hr, ht]
lemma product_ker_nilpotent
    (hχ : ∃ n : ℕ, (RingHom.ker χ.toRingHom) ^ n = ⊥)
    (hψ : ∃ n : ℕ, (RingHom.ker ψ.toRingHom) ^ n = ⊥) :
    ∃ n : ℕ, (RingHom.ker (productAugmentation χ ψ).toRingHom) ^ n = ⊥ := by
  obtain ⟨m, hm⟩ := hχ
  obtain ⟨n, hn⟩ := hψ
  let K := RingHom.ker (productAugmentation χ ψ).toRingHom
  have h₁ := pow_le_comap_pow (RingHom.fst R S) K (RingHom.ker χ.toRingHom)
    (by intro x hx; exact funext (fun i => congrFun hx (Sum.inl i))) m
  have h₂ := pow_le_comap_pow (RingHom.snd R S) K (RingHom.ker ψ.toRingHom)
    (by intro x hx; exact funext (fun i => congrFun hx (Sum.inr i))) n
  rw [hm] at h₁
  rw [hn] at h₂
  refine ⟨m + n, le_bot_iff.mp ?_⟩
  intro x hx
  exact Prod.ext (h₁ (Ideal.pow_le_pow_right (by omega) hx))
    (h₂ (Ideal.pow_le_pow_right (by omega) hx))
end Product

section Opposite
variable {R ι : Type v} [Ring R] [Algebra k R] (χ : R →ₐ[k] (ι → k))
def oppositeAugmentation : Rᵐᵒᵖ →ₐ[k] (ι → k) where
  toFun x := χ x.unop
  map_one' := χ.map_one
  map_zero' := χ.map_zero
  map_add' x y := χ.map_add _ _
  map_mul' x y := by simp [map_mul, mul_comm]
  commutes' r := χ.commutes r
lemma opposite_surjective (hχ : Function.Surjective χ) :
    Function.Surjective (oppositeAugmentation χ) := by
  intro s
  obtain ⟨r, hr⟩ := hχ s
  exact ⟨MulOpposite.op r, hr⟩
lemma unop_mem_pow_ker (n : ℕ) {x : Rᵐᵒᵖ}
    (hx : x ∈ (RingHom.ker (oppositeAugmentation χ).toRingHom) ^ n) :
    x.unop ∈ (RingHom.ker χ.toRingHom) ^ n := by
  induction n generalizing x with
  | zero => simp [Submodule.pow_zero, Ideal.one_eq_top]
  | succ n ih =>
    rw [Submodule.pow_succ] at hx
    rw [Ideal.IsTwoSided.pow_succ]
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro y hy z hz
      exact Ideal.mul_mem_mul hz (ih hy)
    · intro y z hy hz
      exact add_mem hy hz
lemma opposite_ker_nilpotent (hχ : ∃ n : ℕ, (RingHom.ker χ.toRingHom) ^ n = ⊥) :
    ∃ n : ℕ, (RingHom.ker (oppositeAugmentation χ).toRingHom) ^ n = ⊥ := by
  obtain ⟨n, hn⟩ := hχ
  refine ⟨n, le_bot_iff.mp ?_⟩
  intro x hx
  have h := unop_mem_pow_ker χ n hx
  rw [hn] at h
  exact MulOpposite.unop_injective h
end Opposite
end LittleFinitistic.SplitBasic

end
end

end OAI
