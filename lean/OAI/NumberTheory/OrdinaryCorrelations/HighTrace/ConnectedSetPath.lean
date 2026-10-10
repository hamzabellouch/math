import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ConnectedSet

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

lemma connectedSet_path (hG : G.IsAcyclic) {A : Finset V} (hA : ConnectedSet G A)
    {x y : V} (hx : x  ∈  A) (hy : y  ∈  A) (p : G.Walk x y) (hp : p.IsPath) :
    ∀ z  ∈  p.support,z  ∈  A := by
  obtain ⟨q,hq⟩ := hA x hx y hy
  have he := paths_eq hG hp q.toPath.property
  rw [he]
  exact fun z hz => hq z (q.support_toPath_subset_support hz)

omit [DecidableEq V] in
lemma getVert_mem_drop {x y : V} (p : G.Walk x y) {i j : ℕ}
    (hij : i  ≤  j) (hj : j  ≤  p.length) : p.getVert j  ∈  (p.drop i).support := by
  apply Walk.mem_support_iff_exists_getVert.mpr
  refine ⟨j-i,?_,?_⟩
  · rw [Walk.drop_getVert,Nat.add_sub_of_le hij]
  · rw [Walk.drop_length]
    omega

omit [DecidableEq V] in
lemma mem_drop_index {x y z : V} (p : G.Walk x y) {i : ℕ} (hi : i  ≤  p.length)
    (hz : z  ∈  (p.drop i).support) : ∃ j,i  ≤  j ∧ j  ≤  p.length ∧ p.getVert j=z := by
  obtain ⟨k,hk,hkl⟩ := Walk.mem_support_iff_exists_getVert.mp hz
  refine ⟨i+k,by omega,?_,?_⟩
  · rw [Walk.drop_length] at hkl
    omega
  · simpa only [Walk.drop_getVert] using hk

lemma connectedSet_segment (hG : G.IsAcyclic) {A : Finset V} (hA : ConnectedSet G A)
    {x y : V} (p : G.Walk x y) (hp : p.IsPath) {i j k : ℕ}
    (hij : i  ≤  j) (hjk : j  ≤  k) (hk : k  ≤  p.length)
    (hiA : p.getVert i  ∈  A) (hkA : p.getVert k  ∈  A) : p.getVert j  ∈  A := by
  let q := (p.drop i).take (k-i)
  have he : (p.drop i).getVert (k-i)=p.getVert k := by
    rw [Walk.drop_getVert,Nat.add_sub_of_le (hij.trans hjk)]
  have hsub := connectedSet_path hG hA hiA (he.symm ▸ hkA) q ((hp.drop i).take (k-i))
  apply hsub
  apply Walk.mem_support_iff_exists_getVert.mpr
  refine ⟨j-i,?_,?_⟩
  · dsimp [q]
    rw [Walk.take_getVert,inf_eq_right.mpr (Nat.sub_le_sub_right hjk i),
      Walk.drop_getVert,Nat.add_sub_of_le hij]
  · dsimp [q]
    rw [Walk.take_length,Walk.drop_length]
    omega

def segmentIndices {x y : V} (p : G.Walk x y) (A : Finset V) : Finset ℕ :=
  (range (p.length+1)).filter (fun i => p.getVert i  ∈  A)

lemma mem_segmentIndices {x y : V} (p : G.Walk x y) (A : Finset V) (i : ℕ) :
    i  ∈  segmentIndices p A ↔ i  ≤  p.length ∧ p.getVert i  ∈  A := by
  simp [segmentIndices]

def rightGate {x y : V} (p : G.Walk x y) (hp : p.IsPath) (A : Finset V)
    (hne : (segmentIndices p A).Nonempty) : Gate G y A := by
  let r := (segmentIndices p A).max' hne
  have hr := (mem_segmentIndices p A r).mp (max'_mem (segmentIndices p A) hne)
  refine ⟨p.getVert r,hr.2,(p.drop r).reverse,(hp.drop r).reverse,?_⟩
  intro z hz hzq
  have hzd : z  ∈  (p.drop r).support := by simpa using hzq
  obtain ⟨j,hrj,hj,hjz⟩ := mem_drop_index p hr.1 hzd
  have hjA : p.getVert j  ∈  A := hjz ▸ hz
  have hjr : j  ≤  r := le_max' _ _ ((mem_segmentIndices p A j).mpr ⟨hj,hjA⟩)
  have he : j=r := le_antisymm hjr hrj
  simpa only [he] using hjz.symm

lemma Gate.vertex_unique {root : V} {A : Finset V} (g k : Gate G root A)
    (hG : G.IsAcyclic) (hA : ConnectedSet G A) : g.vertex=k.vertex := by
  exact k.first g.vertex g.mem (g.on_path hG hA k.mem k.path k.simple)

lemma segment_interval (hG : G.IsAcyclic) {A : Finset V} (hA : ConnectedSet G A)
    {x y : V} (p : G.Walk x y) (hp : p.IsPath) (hne : (segmentIndices p A).Nonempty) (i : ℕ) :
    i  ∈  segmentIndices p A ↔ (segmentIndices p A).min' hne  ≤  i ∧ i  ≤  (segmentIndices p A).max' hne := by
  constructor
  · intro hi
    exact ⟨min'_le _ _ hi,le_max' _ _ hi⟩
  · rintro ⟨hli,hir⟩
    have hl := (mem_segmentIndices p A _).mp (min'_mem (segmentIndices p A) hne)
    have hr := (mem_segmentIndices p A _).mp (max'_mem (segmentIndices p A) hne)
    exact (mem_segmentIndices p A i).mpr ⟨hir.trans hr.1,
      connectedSet_segment hG hA p hp hli hir hr.1 hl.2 hr.2⟩

end
end OrdinaryCorrelations.Rerooting

end

end OAI
