import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls
import OAI.Probability.CriticalPercolation.Gluing.RelayMoves

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

structure OpenRay (ω : Set E) where
  vertex : ℕ → V
  injective : Function.Injective vertex
  adjacent : ∀ n, (G.openGraph ω).Adj (vertex n) (vertex (n+1))

@[ext]
structure RayPrefix (ω : Set E) (o : V) (n : ℕ) where
  vertex : Fin (n+1) → V
  start : vertex 0=o
  adjacent : ∀ i : Fin n, (G.openGraph ω).Adj (vertex i.castSucc) (vertex i.succ)
  injective : Function.Injective vertex
  ball : ∀ i, vertex i∈G.vertexBall o i.val

lemma openWalk_getVert_ball {ω : Set E} {a b : V} (w : (G.openGraph ω).Walk a b) :
    ∀ n≤w.length, w.getVert n∈G.vertexBall a n := by
  intro n
  induction n with
  | zero => intro _; simpa using G.mem_vertexBall_self a 0
  | succ n ih =>
    intro hn
    exact G.vertexBall_step (ih (by omega))
      (G.openGraph_mono (Set.subset_univ _) (w.adj_getVert_succ (by omega)))

lemma rayPrefix_nonempty (hl : G.LocallyFinite) {ω : Set E} {o : V}
    (hi : (G.cluster ω o).Infinite) (n : ℕ) : Nonempty (G.RayPrefix ω o n) := by
  have hn : ¬G.cluster ω o⊆G.vertexBall o n := fun h => hi ((G.vertexBall_finite hl o n).subset h)
  obtain ⟨b,hb,hbn⟩ := Set.not_subset.mp hn
  obtain ⟨w⟩ := hb
  let p := w.toPath
  have hlen : n<p.val.length := by
    by_contra hn
    have h := G.openWalk_getVert_ball p.val p.val.length le_rfl
    rw [SimpleGraph.Walk.getVert_length] at h
    exact hbn (G.vertexBall_mono o (by omega) h)
  refine ⟨{ vertex := fun i => p.val.getVert i.val
            start := p.val.getVert_zero
            adjacent := ?_
            injective := ?_
            ball := ?_ }⟩
  · intro i
    exact p.val.adj_getVert_succ (by omega)
  · intro i j hij
    apply Fin.ext
    exact p.property.getVert_injOn (by change i.val≤p.val.length; omega)
      (by change j.val≤p.val.length; omega) hij
  · intro i
    exact G.openWalk_getVert_ball p.val i.val (by omega)

lemma rayPrefix_finite (hl : G.LocallyFinite) (ω : Set E) (o : V) (n : ℕ) :
    Finite (G.RayPrefix ω o n) := by
  let := (G.vertexBall_finite hl o n).to_subtype
  let f : G.RayPrefix ω o n → (Fin (n+1) → G.vertexBall o n) := fun p i =>
    ⟨p.vertex i,G.vertexBall_mono o (by omega) (p.ball i)⟩
  apply Finite.of_injective f
  intro p q hpq
  apply RayPrefix.ext
  funext i
  exact congrArg Subtype.val (congrFun hpq i)

def RayPrefix.restrict {ω : Set E} {o : V} {i j : ℕ} (h : i≤j)
    (p : G.RayPrefix ω o j) : G.RayPrefix ω o i where
  vertex k := p.vertex (Fin.castLE (Nat.succ_le_succ h) k)
  start := p.start
  adjacent k := p.adjacent (Fin.castLE h k)
  injective := by
    intro x y heq
    exact Fin.ext (congrArg (fun z : Fin (j+1) => z.val) (p.injective heq))
  ball k := p.ball (Fin.castLE (Nat.succ_le_succ h) k)

lemma RayPrefix.restrict_refl {ω : Set E} {o : V} {i : ℕ} (p : G.RayPrefix ω o i) :
    p.restrict G le_rfl=p := by ext k; rfl

lemma RayPrefix.restrict_trans {ω : Set E} {o : V} {i j k : ℕ}
    (hij : i≤j) (hjk : j≤k) (p : G.RayPrefix ω o k) :
    (p.restrict G hjk).restrict G hij=p.restrict G (hij.trans hjk) := by ext k; rfl

theorem infinite_cluster_openRay (hl : G.LocallyFinite) {ω : Set E} {o : V}
    (hi : (G.cluster ω o).Infinite) : ∃ r : G.OpenRay ω, r.vertex 0=o := by
  let : ∀ n, Finite (G.RayPrefix ω o n) := G.rayPrefix_finite hl ω o
  let : ∀ n, Nonempty (G.RayPrefix ω o n) := G.rayPrefix_nonempty hl hi
  obtain ⟨f,hf⟩ := exists_seq_forall_proj_of_forall_finite (α := fun n => G.RayPrefix ω o n)
    (fun {i j} h p => RayPrefix.restrict G (i := i) (j := j) h p)
    (fun {_} p => p.restrict_refl G) (fun {_ _ _} hij hjk p => p.restrict_trans G hij hjk)
    (fun _ _ => Set.toFinite _)
  let r : ℕ → V := fun n => (f n).vertex ⟨n,Nat.lt_succ_self n⟩
  have hcoh : ∀ i j (h : i≤j), (f j).vertex ⟨i,by omega⟩=r i := by
    intro i j hij
    have h := congrArg (fun p : G.RayPrefix ω o i => p.vertex ⟨i,Nat.lt_succ_self i⟩) (hf hij)
    exact h
  have hinj : Function.Injective r := by
    intro i j hij
    have hh : (f (max i j)).vertex ⟨i,by omega⟩=(f (max i j)).vertex ⟨j,by omega⟩ := by
      rw [hcoh i _ (le_max_left _ _),hcoh j _ (le_max_right _ _),hij]
    exact congrArg Fin.val ((f (max i j)).injective hh)
  have hadj : ∀ n, (G.openGraph ω).Adj (r n) (r (n+1)) := by
    intro n
    have h := (f (n+1)).adjacent ⟨n,Nat.lt_succ_self n⟩
    change (G.openGraph ω).Adj ((f (n+1)).vertex ⟨n,by omega⟩)
      ((f (n+1)).vertex ⟨n+1,by omega⟩) at h
    simpa only [hcoh n (n+1) (Nat.le_succ n),hcoh (n+1) (n+1) le_rfl] using h
  exact ⟨⟨r,hinj,hadj⟩,(f 0).start⟩

theorem infinite_induced_openRay (hl : G.LocallyFinite) (ω : Set E) (S : Set V) (o : V)
    (hi : (G.cluster (ω∩G.inducedEdges S) o).Infinite) :
    ∃ r : G.OpenRay ω, r.vertex 0=o ∧ ∀ n, r.vertex n∈S := by
  obtain ⟨r,hr⟩ := G.infinite_cluster_openRay hl hi
  refine ⟨⟨r.vertex,r.injective,fun n => G.openGraph_mono Set.inter_subset_left (r.adjacent n)⟩,
    hr,?_⟩
  intro n
  exact ((G.open_induced_adj S ω _ _).mp (r.adjacent n)).2.1

lemma no_bounded_ray_rectangles (hl : G.LocallyFinite) (u v : V → ℝ) (ω : Set E)
    (h : ¬∃ r : G.OpenRay ω, ∃ U W : ℝ,
      ∀ n, |u (r.vertex n)|≤U ∧ |v (r.vertex n)|≤W) :
    ∀ U W : ℝ, ∀ a,
      (G.cluster (ω∩G.inducedEdges {x | |u x|≤U ∧ |v x|≤W}) a).Finite := by
  intro U W a
  by_contra hi
  obtain ⟨r,_hr,hS⟩ := G.infinite_induced_openRay hl ω _ a hi
  exact h ⟨r,U,W,hS⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
