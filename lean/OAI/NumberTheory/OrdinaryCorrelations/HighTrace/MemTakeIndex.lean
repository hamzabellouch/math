import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ConnectedSetPath

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.Rerooting
open Classical Finset SimpleGraph
noncomputable section
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
lemma mem_take_index {x y z : V} (p : G.Walk x y) {i : ℕ}
    (hz : z ∈ (p.take i).support) : ∃ j,j ≤ i ∧ j ≤ p.length ∧ p.getVert j=z := by
  obtain ⟨k,hk,hkl⟩ := Walk.mem_support_iff_exists_getVert.mp hz
  rw [Walk.take_length] at hkl
  obtain ⟨hki,hkp⟩ := le_min_iff.mp hkl
  refine ⟨k,hki,hkp,?_⟩
  simpa only [Walk.take_getVert,inf_eq_right.mpr hki] using hk

def leftGate {x y : V} (p : G.Walk x y) (hp : p.IsPath) (A : Finset V)
    (hne : (segmentIndices p A).Nonempty) : Gate G x A := by
  let l := (segmentIndices p A).min' hne
  have hl := (mem_segmentIndices p A l).mp (min'_mem (segmentIndices p A) hne)
  refine ⟨p.getVert l,hl.2,p.take l,hp.take l,?_⟩
  intro z hz hzq
  obtain ⟨j,hjl,hj,hjz⟩ := mem_take_index p hzq
  have hjA : p.getVert j ∈ A := hjz ▸ hz
  have hlj : l ≤ j := min'_le _ _ ((mem_segmentIndices p A j).mpr ⟨hj,hjA⟩)
  have he : j=l := le_antisymm hjl hlj
  simpa only [he] using hjz.symm

lemma Gate.path_unique {root : V} {A : Finset V} (g k : Gate G root A)
    (hG : G.IsAcyclic) (hA : ConnectedSet G A) :
    g.path=k.path.copy rfl (g.vertex_unique k hG hA).symm :=
  paths_eq hG g.simple (by simpa using k.simple)

lemma leftGate_length {x y : V} (p : G.Walk x y) (hp : p.IsPath) (A : Finset V)
    (hne : (segmentIndices p A).Nonempty) :
    (leftGate p hp A hne).path.length=(segmentIndices p A).min' hne := by
  change (p.take _).length=_
  rw [Walk.take_length,inf_eq_left.mpr ((mem_segmentIndices p A _).mp (min'_mem (segmentIndices p A) hne)).1]

lemma rightGate_length {x y : V} (p : G.Walk x y) (hp : p.IsPath) (A : Finset V)
    (hne : (segmentIndices p A).Nonempty) :
    (rightGate p hp A hne).path.length=p.length-(segmentIndices p A).max' hne := by
  change (p.drop _).reverse.length=_
  rw [Walk.length_reverse,Walk.drop_length]

lemma ancestor_length_lt {ι : Type*} (hG : G.IsAcyclic) (root : V) (v : ι→V)
    (p : ∀ i,G.Walk root (v i)) (hp : ∀ i,(p i).IsPath) {i j : ι}
    (hij : Ancestor root v p i j) : (p i).length<(p j).length := by
  have he := paths_eq hG (hp i) ((hp j).takeUntil hij.1)
  rw [he]
  exact (p j).length_takeUntil_lt_length hij.1 hij.2

lemma gate_dependency (hG : G.IsAcyclic) {root : V} {A C : Finset V}
    (hC : ConnectedSet G C) (a : Gate G root A) (c : Gate G root C)
    {z : V} (hz : z ∈ C) (hzp : z ∈ a.path.support) (hne : z≠a.vertex) :
    c.vertex ∈ a.path.support ∧ c.vertex≠a.vertex := by
  have hc := c.on_path hG hC hz (a.path.takeUntil z hzp) (a.simple.takeUntil hzp)
  refine ⟨a.path.support_takeUntil_subset_support hzp hc,?_⟩
  intro he
  have hn := Walk.endpoint_notMem_support_takeUntil a.simple hzp hne.symm
  apply hn
  simpa only [he] using hc

end
end OrdinaryCorrelations.Rerooting

end

end OAI
