import OAI.Combinatorics.Ramsey.CycleClique.Construction.RawPathSystem

namespace OAI

/-! Reordering raw chains, used to bring two chosen chains to the front. -/

namespace CycleClique.Construction.RawPathSystem

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

def reorder (S : RawPathSystem G Q) (C : List (List V)) (hp : C.Perm S.chains) :
    RawPathSystem G Q where
  chains := C
  paths := fun l hl => S.paths l (hp.mem_iff.mp hl)
  disjoint := (List.nodup_flatten.mp (hp.flatten.nodup_iff.mpr S.flatten_nodup)).2
  endpoints := fun l hl => S.endpoints l (hp.mem_iff.mp hl)
  no_clique_steps := fun l hl => S.no_clique_steps l (hp.mem_iff.mp hl)

@[simp] theorem reorder_vertices (S : RawPathSystem G Q) (C : List (List V))
    (hp : C.Perm S.chains) : (S.reorder C hp).vertices = S.vertices := by
  ext v
  simp only [vertices, reorder, List.mem_toFinset]
  exact hp.flatten.mem_iff

@[simp] theorem reorder_amount (S : RawPathSystem G Q) (C : List (List V))
    (hp : C.Perm S.chains) : (S.reorder C hp).amount = S.amount := by
  unfold amount
  rw [reorder_vertices]

@[simp] theorem reorder_assignedCount (S : RawPathSystem G Q) (C : List (List V))
    (hp : C.Perm S.chains) : (S.reorder C hp).assignedCount = S.assignedCount := by
  exact (hp.map (fun l => chainCliqueCount Q l - 1)).sum_eq

theorem bring_two_front (S : RawPathSystem G Q) {l m : List V}
    (hl : l ∈ S.chains) (hm : m ∈ S.chains) (hne : l ≠ m) :
    ∃ R : List (List V), (l :: m :: R).Perm S.chains := by
  have hm' : m ∈ S.chains.erase l := (List.mem_erase_of_ne hne.symm).mpr hm
  exact ⟨(S.chains.erase l).erase m,
    ((List.perm_cons_erase hm').cons l).symm.trans (List.perm_cons_erase hl).symm⟩

theorem disjoint_of_mem (S : RawPathSystem G Q) {l m : List V}
    (hl : l ∈ S.chains) (hm : m ∈ S.chains) (hne : l ≠ m) : l.Disjoint m := by
  obtain ⟨R, hp⟩ := S.bring_two_front hl hm hne
  have hnd := hp.flatten.nodup_iff.mpr S.flatten_nodup
  have hd := (List.nodup_flatten.mp hnd).2
  exact (List.pairwise_cons.mp hd).1 m (by simp)

end CycleClique.Construction.RawPathSystem

end OAI
