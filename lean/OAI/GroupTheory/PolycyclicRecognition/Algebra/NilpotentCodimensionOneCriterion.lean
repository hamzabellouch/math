import Mathlib.Algebra.Lie.Engel
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Basic.Real.Basic

namespace OAI

/-! # Nilpotence in a one-dimensional derivation extension

The ideal acts nilpotently on the extension: the first bracket lands in
the ideal and all subsequent brackets are adjoint operators of the ideal.
Engel's codimension-one criterion then adjoins the nilpotent time operator.
-/

noncomputable section
namespace PolycyclicRecognition

theorem nilpotent_of_codimension_one_restriction
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : Module.End ℝ (V × ℝ)) (a : Module.End ℝ V)
    (ha : IsNilpotent a)
    (hzero : ∀ x, (f x).2 = 0)
    (hres : ∀ x, f (x, 0) = (a x, 0)) : IsNilpotent f := by
  obtain ⟨n, hn⟩ := ha
  have hpow (k : ℕ) (x : V) : (f ^ k) (x, 0) = ((a ^ k) x, 0) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, hres, pow_succ', Module.End.mul_apply]
  refine ⟨n + 1, ?_⟩
  apply LinearMap.ext
  intro x
  rw [pow_succ, Module.End.mul_apply]
  have hx : f x = ((f x).1, 0) := Prod.ext rfl (hzero x)
  rw [hx, hpow, hn]
  rfl

theorem nilpotent_of_split_restriction
    {T V : Type*} [AddCommGroup T] [Module ℝ T] [AddCommGroup V] [Module ℝ V]
    (e : T ≃ₗ[ℝ] (V × ℝ)) (f : Module.End ℝ T) (a : Module.End ℝ V) (ha : IsNilpotent a)
      (hz : ∀ y, (e (f y)).2 = 0)
      (hr : ∀ y, e (f (e.symm (y, 0))) = (a y, 0)) : IsNilpotent f := by
  have hn : IsNilpotent (e.conjRingEquiv f) := by
    apply nilpotent_of_codimension_one_restriction _ a ha
    · intro y; exact hz (e.symm y)
    · exact hr
  obtain ⟨n, hn⟩ := hn
  refine ⟨n, e.conjRingEquiv.injective ?_⟩
  rw [map_pow, hn, map_zero]

variable {L T : Type*} [LieRing L] [LieAlgebra ℝ L]
  [LieRing.IsNilpotent L] [LieRing T] [LieAlgebra ℝ T]
  [FiniteDimensional ℝ T]

theorem nilpotent_derivation_extension
    (e : T ≃ₗ[ℝ] (L × ℝ))
    (D : L →ₗ[ℝ] L) (hD : IsNilpotent D)
    (hb : ∀ x y : T,
      e ⁅x, y⁆ = (⁅(e x).1, (e y).1⁆ + (e x).2 • D (e y).1 -
        (e y).2 • D (e x).1, 0)) : LieRing.IsNilpotent T := by
  let I : LieIdeal ℝ T :=
    { carrier := {x | (e x).2 = 0}
      zero_mem' := by change (e 0).2 = 0; rw [map_zero]; rfl
      add_mem' := by
        intro x y hx hy
        change (e (x + y)).2 = 0
        rw [map_add]
        change (e x).2 + (e y).2 = 0
        rw [hx, hy, add_zero]
      smul_mem' := by
        intro r x hx
        change (e (r • x)).2 = 0
        rw [map_smul]
        change r • (e x).2 = 0
        rw [hx, smul_zero]
      lie_mem := by intro x y _; change (e ⁅x, y⁆).2 = 0; rw [hb] }
  have hideal : LieModule.IsNilpotent I T := by
    apply (LieModule.isNilpotent_iff_forall' (R := ℝ) (L := I) (M := T)).mpr
    intro x
    have hx : (e x.val).2 = 0 := x.property
    apply nilpotent_of_split_restriction e (LieModule.toEnd ℝ I T x) (LieAlgebra.ad ℝ L (e x.val).1)
      (LieModule.isNilpotent_toEnd_of_isNilpotent ℝ L L (e x.val).1)
    · intro y
      change (e ⁅x.val, y⁆).2 = 0
      rw [hb]
    · intro y
      change e ⁅x.val, e.symm (y, 0)⁆ = (⁅(e x.val).1, y⁆, 0)
      rw [hb, e.apply_symm_apply]
      simp only [hx, zero_smul, add_zero, sub_zero]
  let t : T := e.symm (0, 1)
  have ht : e t = (0, 1) := e.apply_symm_apply _
  have htime : IsNilpotent (LieModule.toEnd ℝ T T t) := by
    apply nilpotent_of_split_restriction e _ D hD
    · intro y
      change (e ⁅t, y⁆).2 = 0
      rw [hb]
    · intro y
      change e ⁅t, e.symm (y, 0)⁆ = (D y, 0)
      rw [hb, ht, e.apply_symm_apply]
      simp only [zero_lie, one_smul, zero_smul, zero_add, sub_zero]
  have hspan : ℝ ∙ t ⊔ I.toSubmodule = ⊤ := by
    apply top_unique
    intro x _
    apply Submodule.mem_sup.mpr
    refine ⟨(e x).2 • t, Submodule.smul_mem _ _
      (Submodule.mem_span_singleton_self _), e.symm ((e x).1, 0), ?_, ?_⟩
    · change (e (e.symm ((e x).1, 0))).2 = 0
      rw [e.apply_symm_apply]
    · apply e.injective
      rw [map_add, map_smul, ht, e.apply_symm_apply]
      apply Prod.ext
      · change (e x).2 • (0 : L) + (e x).1 = (e x).1
        rw [smul_zero, zero_add]
      · change (e x).2 * 1 + 0 = (e x).2
        rw [mul_one, add_zero]
  exact LieSubmodule.isNilpotentOfIsNilpotentSpanSupEqTop
    (R := ℝ) (L := T) (M := T) (I := I) (x := t) hspan htime hideal

end PolycyclicRecognition

end

end OAI
