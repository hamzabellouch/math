import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod
import OAI.Computability.BinPacking.Inventory.InventoryScores

namespace OAI

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

theorem card_jobCopy_edge_of_endpoint (v : D.Vertex) (e : D.Edge) (s : Fin 2)
    (hs : D.graph.endpoint e s = v) :
    (Finset.univ.filter (fun j : D.JobCopy v => (D.jobPosition j).1 = e)).card =
      D.d * D.R := by
  classical
  let f : Fin D.R × Fin D.d → D.JobCopy v :=
    fun rc => ((⟨(e, s), hs⟩, rc.1), rc.2)
  have hf : Function.Injective f := by
    intro a b hab
    apply Prod.ext
    · exact congrArg (fun j : D.JobCopy v => j.1.2) hab
    · exact congrArg (fun j : D.JobCopy v => j.2) hab
  have hfilter :
      Finset.univ.filter (fun j : D.JobCopy v => (D.jobPosition j).1 = e) =
        Finset.univ.image f := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hj
      apply Finset.mem_image.mpr
      refine ⟨(j.1.2, j.2), Finset.mem_univ _, ?_⟩
      rcases j with ⟨⟨⟨⟨e', s'⟩, hv⟩, r⟩, c⟩
      change e' = e at hj
      subst e'
      have hslot : s = s' := D.graph.endpoint_injective e (hs.trans hv.symm)
      subst s'
      rfl
    · intro hj
      obtain ⟨rc, _, rfl⟩ := Finset.mem_image.mp hj
      rfl
  rw [hfilter, Finset.card_image_of_injective _ hf, Finset.card_univ]
  simp [Nat.mul_comm]

theorem card_jobCopy_edge (v : D.Vertex) (e : D.Edge) :
    (Finset.univ.filter (fun j : D.JobCopy v => (D.jobPosition j).1 = e)).card =
      if D.graph.left e = v ∨ D.graph.right e = v then D.d * D.R else 0 := by
  classical
  by_cases hv : D.graph.left e = v ∨ D.graph.right e = v
  · rw [ite_eq_left hv]
    rcases hv with hl | hr
    · exact D.card_jobCopy_edge_of_endpoint v e 0 (by simpa using hl)
    · exact D.card_jobCopy_edge_of_endpoint v e 1 (by simpa using hr)
  · rw [ite_eq_right hv]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    apply hv
    have he : j.1.1.val.1 = e := (Finset.mem_filter.mp hj).2
    have hep : D.graph.endpoint e j.1.1.val.2 = v := by
      rw [← he]
      exact j.1.1.property
    have hslot : j.1.1.val.2 = 0 ∨ j.1.1.val.2 = 1 := by omega
    rcases hslot with hzero | hone
    · left
      simpa only [hzero, GraphInput.endpoint_zero] using hep
    · right
      simpa only [hone, GraphInput.endpoint_one] using hep

theorem sum_card_jobCopy_edge (e : D.Edge) :
    (∑ v : D.Vertex,
      (Finset.univ.filter (fun j : D.JobCopy v => (D.jobPosition j).1 = e)).card) =
      2 * D.d * D.R := by
  classical
  calc
    _ =
        (Finset.univ.filter (fun j : D.JobCopy (D.graph.left e) =>
          (D.jobPosition j).1 = e)).card +
        (Finset.univ.filter (fun j : D.JobCopy (D.graph.right e) =>
          (D.jobPosition j).1 = e)).card := by
      refine Finset.sum_eq_add_of_mem (D.graph.left e) (D.graph.right e)
        (Finset.mem_univ _) (Finset.mem_univ _) (D.graph.left_ne_right e) ?_
      intro v _ hv
      rw [D.card_jobCopy_edge]
      simp [Ne.symm hv.1, Ne.symm hv.2]
    _ = D.d * D.R + D.d * D.R := by simp [D.card_jobCopy_edge]
    _ = 2 * D.d * D.R := by simp [two_mul, Nat.add_mul]

end BinPackingGap.InventoryData

end OAI
