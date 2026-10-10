import OAI.Combinatorics.ContingencyTables.Transport.ResidualSearch

namespace OAI

/-! # Bounded shortest-path labels for Edmonds--Karp

An unreachable vertex has label n. Reachable vertices have their actual
shortest distance, at most n-1. These labels are obtained from the already
proved breadth-first search, independently of its deterministic tie rule.
-/
namespace ContingencyTables.EdmondsKarpDistance
open FiniteDirectedBFS PublishedEdmondsKarp
open scoped Classical
noncomputable section
variable {n : ℕ}

def distance (E : Fin n→Fin n→Bool) (s v : Fin n) : ℕ :=
  ((paths E s n v).map (fun xs => xs.length-1)).getD n

lemma distance_of_some {E : Fin n→Fin n→Bool} {s v : Fin n} {xs : List (Fin n)}
    (h : paths E s n v=some xs) : distance E s v=xs.length-1 := by
  simp only [distance,h,Option.map_some,Option.getD_some]

lemma distance_of_none {E : Fin n→Fin n→Bool} {s v : Fin n}
    (h : paths E s n v=none) : distance E s v=n := by
  simp only [distance,h,Option.map_none,Option.getD_none]

lemma distance_le (E : Fin n→Fin n→Bool) (s v : Fin n) : distance E s v ≤ n := by
  cases h : paths E s n v with
  | none => exact (distance_of_none h).le
  | some xs =>
    rw [distance_of_some h]
    have hl := paths_length_le h
    omega

lemma distance_lt_of_some {E : Fin n→Fin n→Bool} {s v : Fin n} {xs : List (Fin n)}
    (h : paths E s n v=some xs) : distance E s v < n := by
  rw [distance_of_some h]
  have hl := paths_length_le h
  have hp := (paths_sound h).1.length_pos
  omega

lemma distance_source (E : Fin n→Fin n→Bool) (s : Fin n) : distance E s s=0 := by
  obtain ⟨xs,hxs⟩ := source_found E s
  rw [distance_of_some hxs]
  have hshort := paths_shortest hxs [s] Route.start
  simp only [List.length_singleton] at hshort
  omega

lemma distance_route {E : Fin n→Fin n→Bool} {s v : Fin n} {xs : List (Fin n)}
    (h : Route E s v xs) : distance E s v ≤ xs.length-1 := by
  obtain ⟨ys,hys⟩ := route_found h
  rw [distance_of_some hys]
  exact Nat.sub_le_sub_right (paths_shortest hys xs h) 1

lemma distance_edge {E : Fin n→Fin n→Bool} {s u v : Fin n}
    (he : E u v=true) : distance E s v ≤ distance E s u+1 := by
  cases h : paths E s n u with
  | none =>
    rw [distance_of_none h]
    exact (distance_le E s v).trans (Nat.le_succ n)
  | some xs =>
    have hr := (paths_sound h).1
    have hv := distance_route (hr.extend he)
    rw [distance_of_some h]
    simp only [List.length_append,List.length_singleton] at hv
    have hp := hr.length_pos
    omega

lemma route_potential {E : Fin n→Fin n→Bool} {s v : Fin n} {xs : List (Fin n)}
    (d : Fin n→ℕ) (hzero : d s=0)
    (hedge : ∀ u v,E u v=true → d v ≤ d u+1)
    (h : Route E s v xs) : d v ≤ xs.length-1 := by
  induction h with
  | start => simp only [hzero,List.length_singleton,Nat.sub_self,le_refl]
  | @extend u v xs hr huv ih =>
    have he := hedge u v huv
    have hp := hr.length_pos
    simp only [List.length_append,List.length_singleton]
    omega

/-- Every bounded potential increasing by at most one on each edge lies
below the shortest-path labels. This also covers unreachable vertices. -/
lemma potential_le_distance (E : Fin n→Fin n→Bool) (s : Fin n) (d : Fin n→ℕ)
    (hzero : d s=0) (hbound : ∀ v,d v ≤ n)
    (hedge : ∀ u v,E u v=true → d v ≤ d u+1) (v : Fin n) :
    d v ≤ distance E s v := by
  cases h : paths E s n v with
  | none => simpa only [distance_of_none h] using hbound v
  | some xs =>
    rw [distance_of_some h]
    exact route_potential d hzero hedge (paths_sound h).1

/-- A unit-Lipschitz sequence attaining its maximal endpoint slope has
unit slope at every intermediate index. -/
lemma tight_sequence {k : ℕ} (d : Fin (k+1)→ℕ) (hzero : d 0=0)
    (hlast : d (Fin.last k)=k)
    (hstep : ∀ i : Fin k,d i.succ ≤ d i.castSucc+1) :
    ∀ i : Fin (k+1),d i=i.val := by
  have hu : ∀ i : Fin (k+1),d i ≤ i.val := by
    intro i
    refine Fin.induction ?_ (fun j ih => ?_) i
    · simpa only [Fin.val_zero,hzero] using (Nat.le_refl 0)
    · have hs := hstep j
      simp only [Fin.val_succ,Fin.val_castSucc] at *
      omega
  have hl : ∀ i : Fin (k+1),k ≤ d i+(k-i.val) := by
    intro i
    refine Fin.reverseInduction ?_ (fun j ih => ?_) i
    · simp only [Fin.val_last,hlast,Nat.sub_self,Nat.add_zero,le_refl]
    · have hs := hstep j
      have hj := j.isLt
      simp only [Fin.val_succ,Fin.val_castSucc] at *
      omega
  intro i
  have hupper := hu i
  have hlower := hl i
  have hi := i.isLt
  omega

def label (c : Capacity n) (f : Flow n) (s v : Fin n) : ℕ :=
  distance (ResidualSearch.edge c f) s v

lemma label_le (c : Capacity n) (f : Flow n) (s v : Fin n) : label c f s v ≤ n :=
  distance_le _ _ _

lemma label_source (c : Capacity n) (f : Flow n) (s : Fin n) : label c f s s=0 :=
  distance_source _ _

lemma label_edge {c : Capacity n} {f : Flow n} {s u v : Fin n}
    (h : 0 < (c u v:ℤ)-f u v) : label c f s v ≤ label c f s u+1 :=
  distance_edge (by simpa only [ResidualSearch.edge,decide_eq_true_eq] using h)

lemma label_target {c : Capacity n} {f : Flow n} {s t : Fin n} {k : ℕ}
    {p : Fin (k+1)→Fin n} (hp : ResidualPath c f s t k p)
    (hshort : ∀ l q,ResidualPath c f s t l q → k ≤ l) : label c f s t=k := by
  have hr := ResidualSearch.route_of_residual c f s t k p hp
  obtain ⟨xs,hxs⟩ := route_found hr
  obtain ⟨l,q,hq,hres,_⟩ := ResidualSearch.search_shortest c f s t xs hxs
  have hkl := hshort l q hres
  have hlen : xs.length=l+1 := by rw [hq,List.length_ofFn]
  have hshorter := paths_shortest hxs (List.ofFn p) hr
  simp only [List.length_ofFn] at hshorter
  change distance (ResidualSearch.edge c f) s t=k
  rw [distance_of_some hxs]
  omega

/-- Every vertex of a shortest residual augmenting path has its path
index as shortest distance from the source. -/
theorem label_path {c : Capacity n} {f : Flow n} {s t : Fin n} {k : ℕ}
    {p : Fin (k+1)→Fin n} (hp : ResidualPath c f s t k p)
    (hshort : ∀ l q,ResidualPath c f s t l q → k ≤ l) (i : Fin (k+1)) :
    label c f s (p i)=i.val := by
  apply tight_sequence (fun j => label c f s (p j))
  · rw [hp.1,label_source]
  · rw [hp.2.1]
    exact label_target hp hshort
  · intro j
    exact label_edge (hp.2.2.2 j)

lemma label_path_lt {c : Capacity n} {f : Flow n} {s t : Fin n} {k : ℕ}
    {p : Fin (k+1)→Fin n} (hp : ResidualPath c f s t k p)
    (hshort : ∀ l q,ResidualPath c f s t l q → k ≤ l) (i : Fin (k+1)) :
    label c f s (p i) < n := by
  rw [label_path hp hshort]
  have hcard := Fintype.card_le_of_injective p hp.2.2.1
  simp only [Fintype.card_fin] at hcard
  have hi := i.isLt
  omega

end
end ContingencyTables.EdmondsKarpDistance

end OAI
