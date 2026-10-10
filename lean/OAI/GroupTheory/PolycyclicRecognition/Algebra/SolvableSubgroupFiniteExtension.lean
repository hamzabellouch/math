import OAI.GroupTheory.PolycyclicRecognition.Algebra.BoundedLocallyFiniteKernel
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace OAI

/-! # A solvable normal subgroup with finite index in the height kernel -/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem quotientImage_finite_of_relative_finiteIndex (S N : Subgroup G) [S.Normal]
    [(S.subgroupOf N).FiniteIndex] : Finite (N.map (QuotientGroup.mk' S)) := by
  let f := (QuotientGroup.mk' S).comp N.subtype
  have hk : f.ker = S.subgroupOf N := by
    ext n
    change (QuotientGroup.mk' S) (n : G) = 1 ↔ (n : G) ∈ S
    exact QuotientGroup.eq_one_iff (n : G)
  let : f.ker.FiniteIndex := hk.symm ▸ inferInstance
  have hr : f.range = N.map (QuotientGroup.mk' S) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hr]
  exact Nat.finite_of_card_ne_zero (by
    rw [← Subgroup.index_ker]
    exact Subgroup.FiniteIndex.index_ne_zero)

theorem virtuallySolvable_of_relative_finiteIndex_solvable
    (S N : Subgroup G) [S.Normal] [N.Normal] (hSN : S ≤ N)
    [Group.IsSolvable S] [(S.subgroupOf N).FiniteIndex] [Group.IsSolvable (G ⧸ N)] :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H := by
  let q := QuotientGroup.mk' S
  let M := N.map q
  let : Finite M := quotientImage_finite_of_relative_finiteIndex S N
  let e := QuotientGroup.quotientQuotientEquivQuotient S N hSN
  let : Group.IsSolvable ((G ⧸ S) ⧸ M) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let : Finite (QuotientGroup.mk' M).ker := by
    simpa only [QuotientGroup.ker_mk'] using (inferInstance : Finite M)
  obtain ⟨V, hVi, hVs⟩ := virtually_solvable_of_finite_kernel (QuotientGroup.mk' M)
  let := hVi
  let := hVs
  let H := V.comap q
  let p : H →* V := (q.comp H.subtype).codRestrict V (fun x => x.property)
  let j : p.ker →* S :=
    { toFun x := ⟨((x : H) : G), (QuotientGroup.eq_one_iff _).mp
        (congrArg (fun v : V => (v : G ⧸ S)) x.property)⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun s : S => (s : G)) hxy
  let : Group.IsSolvable p.ker := Group.isSolvable_of_isSolvable_injective (f := j) hj
  let : Group.IsSolvable H :=
    Group.isSolvable_of_ker_le_range p.ker.subtype p (by simp)
  exact ⟨H, inferInstance, inferInstance⟩

end PolycyclicRecognition

end

end OAI
