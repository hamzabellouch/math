import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Chain
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

namespace OAI

/-! # Deterministic directed breadth-first search

Each round retains every discovered path and scans the vertex list for
one predecessor of each undiscovered vertex. There is one stored path
per vertex; the search does not enumerate candidate paths.
-/

namespace ContingencyTables.FiniteDirectedBFS

variable {n : ℕ}

/-- A directed walk, including its two endpoints. -/
inductive Route (E : Fin n → Fin n → Bool) (s : Fin n) :
    Fin n → List (Fin n) → Prop
  | start : Route E s s [s]
  | extend {u v xs} : Route E s u xs → E u v=true → Route E s v (xs++[v])

namespace Route

variable {E : Fin n → Fin n → Bool} {s v : Fin n} {xs : List (Fin n)}

theorem nonempty (h : Route E s v xs) : xs≠[] := by
  cases h <;> simp

theorem length_pos (h : Route E s v xs) : 0<xs.length :=
  List.length_pos_iff.mpr h.nonempty

theorem head (h : Route E s v xs) : xs.head?=some s := by
  induction h with
  | start => rfl
  | @extend u v xs h _ ih =>
    rw [List.head?_append_of_ne_nil _ h.nonempty]
    exact ih

theorem last (h : Route E s v xs) : xs.getLast?=some v := by
  cases h <;> simp

theorem chain (h : Route E s v xs) : xs.IsChain (fun a b=>E a b=true) := by
  induction h with
  | start => exact List.IsChain.singleton _
  | @extend u v xs h huv ih =>
    apply ih.append (List.IsChain.singleton _)
    simpa [h.last] using huv

/-- Every visited vertex has a prefix walk no longer than the whole walk. -/
theorem routePrefix (h : Route E s v xs) {w : Fin n} (hw : w∈xs) :
    ∃ ys, Route E s w ys ∧ ys.length≤xs.length := by
  induction h with
  | start =>
    have he : w=s := by simpa using hw
    subst w
    exact ⟨[s],Route.start,le_rfl⟩
  | @extend u v xs h huv ih =>
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨ys,hy,hl⟩ := ih hw
      exact ⟨ys,hy,hl.trans (by simp)⟩
    · have he : w=v := by simpa using hw
      subst w
      exact ⟨xs++[v],h.extend huv,le_rfl⟩

end Route

abbrev Paths (n : ℕ) := Fin n → Option (List (Fin n))

def discovered (P : Paths n) (v : Fin n) : Prop := ∃ xs,P v=some xs

def predecessor (E : Fin n → Fin n → Bool) (P : Paths n) (v : Fin n) :
    Option (Fin n) :=
  (List.finRange n).find? (fun u=> (P u).isSome && E u v)

def round (E : Fin n → Fin n → Bool) (P : Paths n) (v : Fin n) :
    Option (List (Fin n)) :=
  match P v with
  | some xs => some xs
  | none => (predecessor E P v).bind (fun u=>(P u).map (fun xs=>xs++[v]))

def paths (E : Fin n → Fin n → Bool) (s : Fin n) : ℕ → Paths n
  | 0 => fun v=>if v=s then some [s] else none
  | k+1 => round E (paths E s k)

lemma predecessor_some {E : Fin n → Fin n → Bool} {P : Paths n}
    {v u : Fin n} (h : predecessor E P v=some u) :
    discovered P u ∧ E u v=true := by
  have hp := List.find?_some h
  simp only [Bool.and_eq_true,Option.isSome_iff_exists] at hp
  exact hp

lemma predecessor_none {E : Fin n → Fin n → Bool} {P : Paths n}
    {v : Fin n} (h : predecessor E P v=none) :
    ∀ u,discovered P u → E u v≠true := by
  have hp := List.find?_eq_none.mp h
  intro u hu he
  have hx := hp u (List.mem_finRange u)
  obtain ⟨xs,hxs⟩ := hu
  simp [hxs,he] at hx

lemma round_retains {E : Fin n → Fin n → Bool} {P : Paths n}
    {v : Fin n} {xs : List (Fin n)} (h : P v=some xs) :
    round E P v=some xs := by simp [round,h]

lemma round_discovered {E : Fin n → Fin n → Bool} {P : Paths n} {v : Fin n} :
    discovered (round E P) v ↔
      discovered P v ∨ ∃ u,discovered P u ∧ E u v=true := by
  cases hv : P v with
  | some xs =>
    constructor
    · intro _; exact Or.inl ⟨xs,hv⟩
    · intro _; exact ⟨xs,round_retains hv⟩
  | none =>
    cases hp : predecessor E P v with
    | none =>
      constructor
      · rintro ⟨xs,hxs⟩
        simp [round,hv,hp] at hxs
      · intro h
        rcases h with ⟨xs,hxs⟩ | ⟨u,hu,he⟩
        · simp [hv] at hxs
        · exact False.elim (predecessor_none hp u hu he)
    | some u =>
      obtain ⟨⟨xs,hxs⟩,huv⟩ := predecessor_some hp
      constructor
      · intro _; exact Or.inr ⟨u,⟨xs,hxs⟩,huv⟩
      · intro _; exact ⟨xs++[v],by simp [round,hv,hp,hxs]⟩

theorem paths_sound {E : Fin n → Fin n → Bool} {s v : Fin n}
    {k : ℕ} {xs : List (Fin n)} (h : paths E s k v=some xs) :
    Route E s v xs ∧ xs.length≤k+1 := by
  induction k generalizing v xs with
  | zero =>
    simp only [paths] at h
    split at h
    · rename_i he
      subst v
      have hx : xs=[s] := by simpa using h.symm
      subst xs
      exact ⟨Route.start,le_rfl⟩
    · simp at h
  | succ k ih =>
    change round E (paths E s k) v=some xs at h
    cases hv : paths E s k v with
    | some ys =>
      have hx : ys=xs := by simpa [round,hv] using h
      subst xs
      obtain ⟨hr,hl⟩ := ih hv
      exact ⟨hr,hl.trans (by omega)⟩
    | none =>
      cases hp : predecessor E (paths E s k) v with
      | none => simp [round,hv,hp] at h
      | some u =>
        obtain ⟨⟨ys,hy⟩,huv⟩ := predecessor_some hp
        have hx : ys++[v]=xs := by simpa [round,hv,hp,hy] using h
        subst xs
        obtain ⟨hr,hl⟩ := ih hy
        exact ⟨hr.extend huv,by simpa using Nat.add_le_add_right hl 1⟩

theorem route_discovered {E : Fin n → Fin n → Bool} {s v : Fin n}
    {xs : List (Fin n)} (h : Route E s v xs) (k : ℕ)
    (hl : xs.length≤k+1) : discovered (paths E s k) v := by
  induction k generalizing v xs with
  | zero =>
    cases h with
    | start => exact ⟨[s],by simp [paths]⟩
    | @extend u v ys hy _ =>
      have hp := hy.length_pos
      simp only [List.length_append,List.length_singleton] at hl
      omega
  | succ k ih =>
    change discovered (round E (paths E s k)) v
    apply round_discovered.mpr
    cases h with
    | start => exact Or.inl (ih Route.start (by simp))
    | @extend u v ys hy huv =>
      exact Or.inr ⟨u,ih hy (by simpa using hl),huv⟩

theorem paths_shortest {E : Fin n → Fin n → Bool} {s v : Fin n}
    {k : ℕ} {xs : List (Fin n)} (h : paths E s k v=some xs) :
    ∀ ys,Route E s v ys → xs.length≤ys.length := by
  induction k generalizing v xs with
  | zero =>
    have ⟨_,hl⟩ := paths_sound h
    intro ys hy
    exact hl.trans (by have hp:=hy.length_pos; omega)
  | succ k ih =>
    cases hv : paths E s k v with
    | some ys =>
      have hx : ys=xs := by simpa [paths,round,hv] using h
      subst xs
      exact ih hv
    | none =>
      intro ys hy
      have hs := (paths_sound h).2
      by_contra hn
      have hl : ys.length≤k+1 := by omega
      obtain ⟨zs,hz⟩ := route_discovered hy k hl
      simp [hv] at hz

theorem paths_nodup {E : Fin n → Fin n → Bool} {s v : Fin n}
    {k : ℕ} {xs : List (Fin n)} (h : paths E s k v=some xs) : xs.Nodup := by
  induction k generalizing v xs with
  | zero =>
    have ⟨hr,_⟩ := paths_sound h
    cases hr with
    | start => simp
    | @extend u v ys hy _ =>
      have hp:=hy.length_pos
      have hl := (paths_sound h).2
      simp only [List.length_append,List.length_singleton] at hl
      omega
  | succ k ih =>
    cases hv : paths E s k v with
    | some ys =>
      have hx : ys=xs := by simpa [paths,round,hv] using h
      subst xs
      exact ih hv
    | none =>
      cases hp : predecessor E (paths E s k) v with
      | none => simp [paths,round,hv,hp] at h
      | some u =>
        obtain ⟨⟨ys,hy⟩,_⟩ := predecessor_some hp
        have hx : ys++[v]=xs := by simpa [paths,round,hv,hp,hy] using h
        subst xs
        have hnot : v∉ys := by
          intro hm
          have ⟨hr,hl⟩ := paths_sound hy
          obtain ⟨zs,hz,hzl⟩ := hr.routePrefix hm
          obtain ⟨ws,hw⟩ := route_discovered hz k (hzl.trans hl)
          simp [hv] at hw
        apply List.nodup_append.mpr
        refine ⟨ih hy,by simp,?_⟩
        intro a ha b hb hab
        have hb' : b=v := by simpa using hb
        exact hnot (hab.trans hb' ▸ ha)

theorem paths_length_le {E : Fin n → Fin n → Bool} {s v : Fin n}
    {k : ℕ} {xs : List (Fin n)} (h : paths E s k v=some xs) : xs.length≤n := by
  simpa using List.Nodup.length_le_card (paths_nodup h)

/-- Every directed walk is found within n rounds. The proof uses the
short simple path stored by the search, rather than enumerating walks. -/
theorem route_found {E : Fin n → Fin n → Bool} {s v : Fin n}
    {xs : List (Fin n)} (h : Route E s v xs) :
    discovered (paths E s n) v := by
  obtain ⟨ys,hy⟩ := route_discovered h xs.length (by omega)
  exact route_discovered (paths_sound hy).1 n
    ((paths_length_le hy).trans (by omega))

theorem paths_complete {E : Fin n → Fin n → Bool} {s v : Fin n} :
    discovered (paths E s n) v ↔ ∃ xs,Route E s v xs := by
  constructor
  · rintro ⟨xs,hxs⟩
    exact ⟨xs,(paths_sound hxs).1⟩
  · rintro ⟨xs,hxs⟩
    exact route_found hxs

/-- The computed reached set contains the source and is closed under
every directed edge. This is the cut certificate used on failure. -/
theorem source_found (E : Fin n → Fin n → Bool) (s : Fin n) :
    discovered (paths E s n) s := route_found Route.start

theorem reached_closed {E : Fin n → Fin n → Bool} {s u v : Fin n}
    (hu : discovered (paths E s n) u) (huv : E u v=true) :
    discovered (paths E s n) v := by
  obtain ⟨xs,hxs⟩ := hu
  exact route_found ((paths_sound hxs).1.extend huv)

theorem failure_no_route {E : Fin n → Fin n → Bool} {s t : Fin n}
    (h : paths E s n t=none) : ¬∃ xs,Route E s t xs := by
  intro hr
  obtain ⟨xs,hxs⟩ := paths_complete.mpr hr
  simp [h] at hxs

end ContingencyTables.FiniteDirectedBFS

end OAI
