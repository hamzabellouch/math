import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.VertexBall
import OAI.Probability.CriticalPercolation.GraphGeometry.OpenGraphIso

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma vertexBall_mono (o : V) : Monotone (G.vertexBall o) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Set.subset_union_left

lemma mem_vertexBall_self (o : V) (n : ℕ) : o ∈ G.vertexBall o n :=
  G.vertexBall_mono o (Nat.zero_le n) rfl

lemma vertexBall_step {o v w : V} {n : ℕ} (hv : v ∈ G.vertexBall o n)
    (he : G.fullGraph.Adj v w) : w ∈ G.vertexBall o (n+1) :=
  Or.inr (Set.mem_iUnion₂.mpr ⟨v,hv,he⟩)

lemma vertexBall_add {o v : V} {n : ℕ} (hv : v ∈ G.vertexBall o n) (m : ℕ) :
    G.vertexBall v m ⊆ G.vertexBall o (n+m) := by
  induction m with
  | zero => simpa only [vertexBall,Nat.add_zero,Set.singleton_subset_iff] using hv
  | succ m ih =>
    rintro w (hw | hw)
    · exact G.vertexBall_mono o (by omega) (ih hw)
    · obtain ⟨z,hz,hzw⟩ := Set.mem_iUnion₂.mp hw
      exact G.vertexBall_step (ih hz) hzw

lemma vertexBall_comm {o v : V} {n : ℕ} : v ∈ G.vertexBall o n ↔ o ∈ G.vertexBall v n := by
  have h : ∀ n (o v : V), v ∈ G.vertexBall o n → o ∈ G.vertexBall v n := by
    intro n
    induction n with
    | zero => intro o v hv; simpa only [vertexBall,Set.mem_singleton_iff] using hv.symm
    | succ n ih =>
      intro o v hv
      rcases hv with hv | hv
      · exact G.vertexBall_mono v (Nat.le_succ n) (ih o v hv)
      · obtain ⟨z,hz,hzv⟩ := Set.mem_iUnion₂.mp hv
        have h1 : z ∈ G.vertexBall v 1 := G.vertexBall_step (G.mem_vertexBall_self v 0) hzv.symm
        simpa only [Nat.add_comm 1] using G.vertexBall_add h1 n (ih o z hz)
  exact ⟨h n o v,h n v o⟩

lemma Aut.fullGraph_adj (φ : G.Aut) (u v : V) :
    G.fullGraph.Adj (φ.vertex u) (φ.vertex v) ↔ G.fullGraph.Adj u v := by
  simpa only [fullGraph,Set.image_univ,Equiv.range_eq_univ] using Aut.adj_map G φ Set.univ u v

lemma Aut.vertexBall_mem (φ : G.Aut) (o v : V) (n : ℕ) :
    φ.vertex v ∈ G.vertexBall (φ.vertex o) n ↔ v ∈ G.vertexBall o n := by
  induction n generalizing v with
  | zero => simp only [vertexBall,Set.mem_singleton_iff,φ.vertex.injective.eq_iff]
  | succ n ih =>
    simp only [vertexBall,Set.mem_union,Set.mem_iUnion,exists_prop,SimpleGraph.mem_neighborSet]
    constructor
    · rintro (h | ⟨z,hz,hzv⟩)
      · exact Or.inl ((ih v).mp h)
      · obtain ⟨w,rfl⟩ := φ.vertex.surjective z
        exact Or.inr ⟨w,(ih w).mp hz,
          (Aut.fullGraph_adj G φ w v).mp hzv⟩
    · rintro (h | ⟨z,hz,hzv⟩)
      · exact Or.inl ((ih v).mpr h)
      · exact Or.inr ⟨φ.vertex z,(ih z).mpr hz,(Aut.fullGraph_adj G φ z v).mpr hzv⟩

lemma Aut.vertexBall_image (φ : G.Aut) (o : V) (n : ℕ) :
    φ.vertex '' G.vertexBall o n = G.vertexBall (φ.vertex o) n := by
  ext v
  obtain ⟨w,rfl⟩ := φ.vertex.surjective v
  simpa only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right] using
    (Aut.vertexBall_mem G φ o w n).symm

lemma Aut.vertexBall_ncard (φ : G.Aut) (o : V) (n : ℕ) :
    (G.vertexBall (φ.vertex o) n).ncard = (G.vertexBall o n).ncard := by
  rw [← Aut.vertexBall_image G φ,Set.ncard_image_of_injective _ φ.vertex.injective]

lemma Aut.incident_singleton_image (φ : G.Aut) (v : V) :
    φ.edge '' G.incidentEdges {v} = G.incidentEdges {φ.vertex v} := by
  ext e
  obtain ⟨f,rfl⟩ := φ.edge.surjective e
  simp only [Set.mem_image,φ.edge.injective.eq_iff,exists_eq_right,incidentEdges,
    Set.mem_ofPred_eq,Set.mem_singleton_iff,exists_eq_left,φ.preserves]
  simp only [Sym2.mem_map,φ.vertex.injective.eq_iff,exists_eq_right]

lemma uniform_incident_bound (hquasi : G.QuasiTransitive) :
    ∃ D : ℕ, 1≤D ∧ ∀ v, (G.incidentEdges {v}).ncard ≤ D := by
  obtain ⟨S,hS,hcover⟩ := hquasi
  let D := 1 + ∑ v ∈ hS.toFinset, (G.incidentEdges {v}).ncard
  refine ⟨D,by dsimp [D]; omega,?_⟩
  intro v
  obtain ⟨z,hz,φ,rfl⟩ := hcover v
  rw [← Aut.incident_singleton_image G φ,Set.ncard_image_of_injective _ φ.edge.injective]
  exact (Finset.single_le_sum (f := fun v => (G.incidentEdges {v}).ncard) (fun _ _ => Nat.zero_le _) (hS.mem_toFinset.mpr hz)).trans (Nat.le_add_left _ _)

lemma uniform_ball_bound (hquasi : G.QuasiTransitive) (n : ℕ) :
    ∃ M : ℕ, ∀ v, (G.vertexBall v n).ncard ≤ M := by
  obtain ⟨S,hS,hcover⟩ := hquasi
  refine ⟨∑ v ∈ hS.toFinset, (G.vertexBall v n).ncard,?_⟩
  intro v
  obtain ⟨z,hz,φ,rfl⟩ := hcover v
  rw [Aut.vertexBall_ncard G φ]
  exact Finset.single_le_sum (f := fun v => (G.vertexBall v n).ncard) (fun _ _ => Nat.zero_le _) (hS.mem_toFinset.mpr hz)

lemma orbit_density_radius (hconnected : G.fullGraph.Connected)
    (hquasi : G.QuasiTransitive) (u : V) :
    ∃ C : ℕ, ∀ v, ∃ φ : G.Aut, φ.vertex u ∈ G.vertexBall v C := by
  obtain ⟨S,hS,hcover⟩ := hquasi
  have hpath : ∀ z : S, ∃ n, u ∈ G.vertexBall z.val n :=
    fun z => G.reachable_mem_vertexBall (hconnected z u)
  choose n hn using hpath
  let := hS.fintype
  let C := ∑ z : S, n z
  refine ⟨C,?_⟩
  intro v
  obtain ⟨z,hz,φ,rfl⟩ := hcover v
  refine ⟨φ,(Aut.vertexBall_mem G φ z u C).mpr ?_⟩
  exact G.vertexBall_mono z (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (⟨z,hz⟩ : S))) (hn ⟨z,hz⟩)

lemma finite_subset_vertexBall (hconnected : G.fullGraph.Connected)
    (o : V) {S : Set V} (hS : S.Finite) : ∃ n, S ⊆ G.vertexBall o n := by
  have hh : ∀ v : S, ∃ n, v.val ∈ G.vertexBall o n :=
    fun v => G.reachable_mem_vertexBall (hconnected o v)
  choose n hn using hh
  let := hS.fintype
  refine ⟨∑ v : S, n v,?_⟩
  intro v hv
  exact G.vertexBall_mono o (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (⟨v,hv⟩ : S))) (hn ⟨v,hv⟩)

end CriticalPercolation.BondGraph
end
end
end

end OAI
