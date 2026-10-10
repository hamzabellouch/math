import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Index

namespace OAI

/-! Finite generation and power subgroups of abelian groups. -/

open scoped BigOperators

namespace FiniteIndexRealization

lemma elementary_finite_of_fg_bounded_exponent (A : Type*) [CommGroup A]
    [Group.FG A] (n : ℕ) (hn : n ≠ 0) (hexp : ∀ a : A, a ^ n = 1) : Finite A := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Monoid.FG A).fg_top
  let eval : (s → Fin n) → A := fun v => ∏ a : s, (a : A) ^ (v a).val
  apply Finite.of_surjective eval
  intro x
  have hx : x ∈ Submonoid.closure (s : Set A) := by rw [hs]; trivial
  obtain ⟨f, _, hf⟩ := Submonoid.mem_closure_finset.mp hx
  refine ⟨fun a => ⟨f a % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩, ?_⟩
  have hmod (a : A) : a ^ (f a % n) = a ^ f a := by
    conv_rhs => rw [← Nat.mod_add_div (f a) n]
    rw [pow_add, pow_mul, hexp, one_pow, mul_one]
  change (∏ a : s, (a : A) ^ (f a % n)) = x
  simp_rw [hmod]
  exact (Finset.prod_coe_sort (s := s) (f := fun a : A => a ^ f a)).trans hf

lemma elementary_finiteIndex_powers (A : Type*) [CommGroup A] [Group.FG A]
    (n : ℕ) (hn : n ≠ 0) : (powMonoidHom (α := A) n).range.FiniteIndex := by
  let P : Subgroup A := (powMonoidHom (α := A) n).range
  have hexp : ∀ q : A ⧸ P, q ^ n = 1 := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective P q
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (N := P) (a ^ n)).mpr ⟨a, rfl⟩
  let : Finite (A ⧸ P) := elementary_finite_of_fg_bounded_exponent (A ⧸ P) n hn hexp
  exact Subgroup.finiteIndex_iff_finite_quotient.mpr inferInstance

end FiniteIndexRealization

end OAI
