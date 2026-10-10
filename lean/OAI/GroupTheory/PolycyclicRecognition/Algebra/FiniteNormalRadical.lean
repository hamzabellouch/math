import OAI.GroupTheory.PolycyclicRecognition.Algebra.BoundedLocallyFiniteKernel
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Preorder.Finite

namespace OAI

/-! # The largest finite normal subgroup under a finite-subgroup order bound -/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem finite_sup_of_normal (H K : Subgroup G) [H.Normal] [Finite H] [Finite K] :
    Finite (H ⊔ K : Subgroup G) := by
  let f : H × K → (H ⊔ K : Subgroup G) := fun p =>
    ⟨(p.1 : G) * p.2, Subgroup.mul_mem_sup p.1.property p.2.property⟩
  apply Finite.of_surjective f
  intro x
  obtain ⟨h, hh, k, hk, he⟩ := Subgroup.mem_sup_of_normal_left.mp x.property
  exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext he⟩

theorem exists_largest_finite_normal (hb : HasBoundedFiniteSubgroupOrders G) :
    ∃ T : Subgroup G, T.Characteristic ∧ Finite T ∧
      ∀ N : Subgroup G, N.Normal → Finite N → N ≤ T := by
  obtain ⟨b, hb⟩ := hb
  let P : Set (Subgroup G) := {N | N.Normal ∧ Finite N}
  have hP : (Nat.card ∘ (fun N : Subgroup G => N) '' P).Finite := by
    apply (Set.finite_Iic b).subset
    rintro n ⟨N, hN, rfl⟩
    exact hb N hN.2
  obtain ⟨T, hT, hmax⟩ := Set.Finite.exists_maximalFor' (fun N : Subgroup G => Nat.card N)
    P hP ⟨⊥, inferInstance, inferInstance⟩
  let := hT.1
  let := hT.2
  have hle (N : Subgroup G) (hn : N.Normal) (hf : Finite N) : N ≤ T := by
    let := hn
    let := hf
    let : Finite (T ⊔ N : Subgroup G) := finite_sup_of_normal T N
    have hcard : Nat.card (T ⊔ N : Subgroup G) ≤ Nat.card T :=
      hmax ⟨inferInstance, inferInstance⟩ (Subgroup.card_le_of_le le_sup_left)
    have he : T = T ⊔ N := Subgroup.eq_of_le_of_card_ge le_sup_left hcard
    exact le_sup_right.trans_eq he.symm
  have hchar : T.Characteristic := by
    apply Subgroup.characteristic_iff_map_le.mpr
    intro e
    let : Finite (T.map e.toMonoidHom) := Finite.of_equiv T
      (T.equivMapOfInjective e.toMonoidHom e.injective).toEquiv
    exact hle _ (Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective) inferInstance
  exact ⟨T, hchar, hT.2, hle⟩

end PolycyclicRecognition

end

end OAI
