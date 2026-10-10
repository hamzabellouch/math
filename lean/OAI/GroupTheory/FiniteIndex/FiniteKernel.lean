import OAI.GroupTheory.FiniteIndex.Powers
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Commutator.Finite
import Mathlib.GroupTheory.OrderOfElement

namespace OAI

/-! Separation of finite kernels over free abelian quotients. -/

namespace FiniteIndexRealization
open scoped IsMulCommutative

theorem finite_kernel_free_abelian_disjoint {E : Type*} [Group E] [Group.FG E]
    (r : Nat) (f : E →* (Fin r → Multiplicative Int)) [Finite f.ker] :
    ∃ J : Subgroup E, J.FiniteIndex ∧ J ⊓ f.ker = ⊥ := by
  classical
  have hcomm : commutatorSet E ⊆ (f.ker : Set E) := by
    intro x hx
    apply Abelianization.commutator_subset_ker f
    rw [commutator_eq_closure]
    exact Subgroup.subset_closure hx
  let : Finite (commutatorSet E) :=
    Set.finite_coe_iff.mpr ((Set.toFinite (f.ker : Set E)).subset hcomm)
  let Z := Subgroup.center E
  let : Z.FiniteIndex := inferInstance
  let : Group.FG Z := Subgroup.fg_of_index_ne_zero Z
  let n := Nat.card f.ker
  have hn : n ≠ 0 := Nat.card_pos.ne'
  let P : Subgroup Z := (powMonoidHom (α := Z) n).range
  let : P.FiniteIndex := elementary_finiteIndex_powers Z n hn
  let J : Subgroup E := P.map Z.subtype
  have hJ : J.FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, Subgroup.index_map_subtype]
    exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.FiniteIndex.index_ne_zero
  refine ⟨J, hJ, ?_⟩
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro x hx
  obtain ⟨z, hz, rfl⟩ := hx.1
  obtain ⟨w, hw⟩ := hz
  have hwpow : (w : E) ^ n = (z : E) := congrArg Subtype.val hw
  have hfpow : (f (w : E)) ^ n = 1 := by
    rw [← map_pow, hwpow]
    exact hx.2
  have hfw : f (w : E) = 1 := by
    funext i
    apply pow_left_injective hn
    simpa only [Pi.pow_apply, Pi.one_apply, one_pow] using congrFun hfpow i
  let wk : f.ker := ⟨(w : E), hfw⟩
  have hkill : wk ^ n = 1 := pow_card_eq_one'
  have hkillE : (w : E) ^ n = 1 := congrArg Subtype.val hkill
  exact hwpow.symm.trans hkillE

end FiniteIndexRealization

end OAI
