import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarseEquivalence
import Mathlib.GroupTheory.Finiteness

namespace OAI

/-! # Finite generation is preserved by discrete-group coarse equivalence. -/

namespace PolycyclicRecognition

variable {G H : Type*} [Group G] [Group H]

/-- Coarse connectedness, expressed by finite generation, transfers through the
finite-difference control and finite error sets of a coarse equivalence. -/
theorem GroupCoarseEquivalence.finitelyGenerated (e : GroupCoarseEquivalence G H)
    [Group.FG G] : Group.FG H := by
  classical
  obtain ⟨S, hS, hSfinite⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  obtain ⟨T, hT, hcontrol⟩ := e.bornologous_toFun S hSfinite
  let E := Set.range fun y => y⁻¹ * e.toFun (e.invFun y)
  let U := T ∪ E ∪ {e.toFun 1}
  have hU : U.Finite := (hT.union e.right_error).union (Set.finite_singleton _)
  let K := Subgroup.closure U
  have hTmem {t : H} (ht : t ∈ T) : t ∈ K :=
    Subgroup.subset_closure (Or.inl (Or.inl ht))
  have hsteps : ∀ a : G, ∀ x : G, (e.toFun x)⁻¹ * e.toFun (x * a) ∈ K := by
    intro a
    have ha : a ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top a
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      intro x
      exact hTmem (hcontrol x (x * a) (by simpa using ha))
    | one =>
      intro x
      simp
    | mul a b _ _ ia ib =>
      intro x
      have hm := K.mul_mem (ia x) (ib (x * a))
      simpa only [mul_assoc, mul_inv_cancel_left] using hm
    | inv a _ ia =>
      intro x
      have hi := K.inv_mem (ia (x * a⁻¹))
      simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right,
        mul_inv_rev, inv_inv, inv_mul_cancel, mul_one] using hi
  apply Group.fg_iff.mpr
  refine ⟨U, top_unique ?_, hU⟩
  intro y _
  have hbase : e.toFun 1 ∈ K := Subgroup.subset_closure (Or.inr (Set.mem_singleton _))
  have himage : e.toFun (e.invFun y) ∈ K := by
    simpa using K.mul_mem hbase (hsteps (e.invFun y) 1)
  have herr : y⁻¹ * e.toFun (e.invFun y) ∈ K :=
    Subgroup.subset_closure (Or.inl (Or.inr ⟨y, rfl⟩))
  simpa only [mul_inv_rev, inv_inv, mul_inv_cancel_left] using
    K.mul_mem himage (K.inv_mem herr)

end PolycyclicRecognition

end OAI
