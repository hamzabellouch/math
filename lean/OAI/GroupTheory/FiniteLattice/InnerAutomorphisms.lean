import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.IsPerfect

namespace OAI

/-! Inner automorphisms of nonabelian simple groups. -/
namespace SimpleInnerAutomorphisms

variable (T : Type*) [Group T]

/-- The subgroup of inner automorphisms. -/
def inner : Subgroup (MulAut T) := (MulAut.conj : T →* MulAut T).range

/-- Conjugation is natural under every automorphism. -/
theorem conjugate_conj (b : MulAut T) (t : T) :
    b * MulAut.conj t * b⁻¹ = MulAut.conj (b t) := by
  apply MulEquiv.ext
  intro z
  simp only [MulAut.coe_mul, Function.comp_apply, MulAut.coe_inv,
    MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]

/-- Inner automorphisms form a normal subgroup, for any group. -/
theorem inner_normal : (inner T).Normal := by
  constructor
  intro a ha b
  obtain ⟨t, rfl⟩ := (MonoidHom.mem_range.mp ha)
  exact MonoidHom.mem_range.mpr ⟨b t, (conjugate_conj T b t).symm⟩

variable {T} [IsSimpleGroup T]

/-- Noncommutativity rules out a total kernel of conjugation; simplicity
forces its kernel to be trivial. -/
theorem conj_injective (hna : ∃ x y : T, x * y ≠ y * x) :
    Function.Injective (MulAut.conj : T →* MulAut T) := by
  apply (MonoidHom.ker_eq_bot_iff (MulAut.conj : T →* MulAut T)).mp
  rcases (inferInstance : (MulAut.conj : T →* MulAut T).ker.Normal).eq_bot_or_eq_top
    with hbot | htop
  · exact hbot
  · obtain ⟨x, y, hxy⟩ := hna
    have hx : x ∈ (MulAut.conj : T →* MulAut T).ker := by
      rw [htop]
      exact Subgroup.mem_top x
    have he : MulAut.conj x = (1 : MulAut T) := MonoidHom.mem_ker.mp hx
    have hy := DFunLike.congr_fun he y
    have hconj : x * y * x⁻¹ = y := by
      simpa only [MulAut.conj_apply, MulAut.coe_one, id_eq] using hy
    exact False.elim (hxy (by
      have h := congrArg (fun z : T => z * x) hconj
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using h))

/-- The derived subgroup is normal; simplicity and noncommutativity force
it to be the whole group. -/
theorem perfect_of_simple (hna : ∃ x y : T, x * y ≠ y * x) :
    Group.IsPerfect T := by
  apply Group.isPerfect_def.mpr
  rcases (inferInstance : (commutator T).Normal).eq_bot_or_eq_top with hbot | htop
  · have hc : IsMulCommutative T := (commutator_eq_bot_iff T).mp hbot
    obtain ⟨x, y, hxy⟩ := hna
    exact False.elim (hxy ((isMulCommutative_iff.mp hc) x y))
  · exact htop

/-- A nonabelian simple group is canonically isomorphic to its inner automorphism group. -/
noncomputable def innerEquiv (hna : ∃ x y : T, x * y ≠ y * x) :
    T ≃* inner T := MonoidHom.ofInjective (conj_injective hna)

/-- The canonical isomorphism sends an element to conjugation by that element. -/
theorem innerEquiv_apply (hna : ∃ x y : T, x * y ≠ y * x) (t : T) :
    ((innerEquiv hna t : inner T) : MulAut T) = MulAut.conj t :=
  MonoidHom.ofInjective_apply (conj_injective hna)

/-- The inner automorphism group of a nonabelian simple group is perfect. -/
theorem inner_perfect (hna : ∃ x y : T, x * y ≠ y * x) :
    Group.IsPerfect (inner T) := by
  have : Group.IsPerfect T := perfect_of_simple hna
  exact Group.IsPerfect.range (MulAut.conj : T →* MulAut T)

end SimpleInnerAutomorphisms

end OAI
