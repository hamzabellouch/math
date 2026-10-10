import OAI.Combinatorics.Ramsey.CycleClique.Construction.GlobalLongest
import OAI.Combinatorics.Ramsey.CycleClique.Construction.PathRotation

namespace OAI

/-! A connected graph of minimum degree s has a path of order at least min(|V|,2s+1). -/

namespace CycleClique.Construction
private theorem last_degree_index_bound {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {r : ℕ} {f : Fin (r + 1) → V}
    (hcover : ∀ v, G.Adj (f (Fin.last r)) v → v ∈ Set.range f) :
    (G.neighborSet (f (Fin.last r))).ncard ≤
      (Finset.univ.filter (fun i : Fin r => G.Adj (f (Fin.last r)) (f i.castSucc))).card := by
  classical
  let A := Finset.univ.filter (fun i : Fin r => G.Adj (f (Fin.last r)) (f i.castSucc))
  have hsub : G.neighborFinset (f (Fin.last r)) ⊆ A.image (fun i => f i.castSucc) := by
    intro v hv
    have hadj := (G.mem_neighborFinset _ _).mp hv
    obtain ⟨j, hj⟩ := hcover v hadj
    have hjne : j ≠ Fin.last r := fun h => hadj.ne (by simpa only [h] using hj)
    have hjlt : j.val < r := by
      have := j.isLt
      have hneq : j.val ≠ r := fun h => hjne (Fin.ext h)
      omega
    let i : Fin r := ⟨j.val, hjlt⟩
    have hij : i.castSucc = j := Fin.ext rfl
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, ?_⟩
    · simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      rwa [hij, hj]
    · simpa only [hij] using hj
  have h := (Finset.card_le_card hsub).trans (Finset.card_image_le)
  simpa only [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.ncard_neighborSet] using h

private theorem first_degree_index_bound {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {r : ℕ} {f : Fin (r + 1) → V}
    (hcover : ∀ v, G.Adj (f 0) v → v ∈ Set.range f) :
    (G.neighborSet (f 0)).ncard ≤
      (Finset.univ.filter (fun i : Fin r => G.Adj (f 0) (f i.succ))).card := by
  classical
  let B := Finset.univ.filter (fun i : Fin r => G.Adj (f 0) (f i.succ))
  have hsub : G.neighborFinset (f 0) ⊆ B.image (fun i => f i.succ) := by
    intro v hv
    have hadj := (G.mem_neighborFinset _ _).mp hv
    obtain ⟨j, hj⟩ := hcover v hadj
    have hjne : j ≠ 0 := fun h => hadj.ne (by simpa only [h] using hj)
    have hjpos : 1 ≤ j.val := by
      have hneq : j.val ≠ 0 := fun h => hjne (Fin.ext (by simpa only [Fin.val_zero] using h))
      omega
    let i : Fin r := ⟨j.val - 1, by have := j.isLt; omega⟩
    have hij : i.succ = j := by apply Fin.ext; dsimp [i]; omega
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, ?_⟩
    · simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      rwa [hij, hj]
    · simpa only [hij] using hj
  have h := (Finset.card_le_card hsub).trans (Finset.card_image_le)
  simpa only [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.ncard_neighborSet] using h

/-- Manuscript Lemma `clq:long-path`, in the application-sized form. -/
theorem connected_long_path {V : Type*} [Fintype V] {G : SimpleGraph V} {s k : ℕ}
    (hconn : G.Connected) (hdegree : ∀ v, s ≤ (G.neighborSet v).ncard)
    (hk : k ≤ 2 * s + 1) (hcard : k ≤ Fintype.card V) :
    ∃ r, ∃ f : Fin (r + 1) → V, IsIndexedPath G f ∧ k ≤ r + 1 := by
  classical
  let : Nonempty V := hconn.nonempty
  obtain ⟨r, f, hf, hmax⟩ := exists_longest_path G
  refine ⟨r, f, hf, ?_⟩
  by_contra hshort
  have hlast : ∀ v, G.Adj (f (Fin.last r)) v → v ∈ Set.range f :=
    longest_path_endpoint_neighbors hf rfl (fun q g hg _ => hmax q g hg)
  have hfirst : ∀ v, G.Adj (f 0) v → v ∈ Set.range f := by
    intro v hv
    have hrev := longest_path_endpoint_neighbors (indexedPath_reverse hf) rfl
      (fun q g hg _ => hmax q g hg) v (by simpa using hv)
    obtain ⟨j, hj⟩ := hrev
    exact ⟨j.rev, hj⟩
  let A := Finset.univ.filter (fun i : Fin r => G.Adj (f (Fin.last r)) (f i.castSucc))
  let B := Finset.univ.filter (fun i : Fin r => G.Adj (f 0) (f i.succ))
  have hA : s ≤ A.card := (hdegree _).trans (last_degree_index_bound hlast)
  have hB : s ≤ B.card := (hdegree _).trans (first_degree_index_bound hfirst)
  have hnotdisjoint : ¬ Disjoint A B := by
    intro hdisjoint
    have h := Finset.card_union_of_disjoint hdisjoint
    have hbound : (A ∪ B).card ≤ r := by
      have hsub : A ∪ B ⊆ Finset.univ := Finset.subset_univ _
      simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card hsub
    omega
  obtain ⟨p, hpA, hpB⟩ := Finset.not_disjoint_iff.mp hnotdisjoint
  have hpA' := (Finset.mem_filter.mp hpA).2
  have hpB' := (Finset.mem_filter.mp hpB).2
  obtain ⟨hrotinj, hrotchain, hrotfirst, hrotlast, _⟩ := rotate_path f hf.1 hf.2 p hpA'
  have hrot : IsIndexedPath G (f ∘ rotationIndex p) := ⟨hrotinj, hrotchain⟩
  have hclose : G.Adj ((f ∘ rotationIndex p) (Fin.last r)) ((f ∘ rotationIndex p) 0) := by
    rw [hrotfirst, hrotlast]
    exact hpB'.symm
  have hsurj := closed_longest_path_surjective hconn hrot hmax hclose
  have hfull := Fintype.card_le_of_surjective _ hsurj
  simp only [Fintype.card_fin] at hfull
  omega

end CycleClique.Construction

end OAI
