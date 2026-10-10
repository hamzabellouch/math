import OAI.Computability.MatchingCount.CutAlgebra

namespace OAI

section

namespace BinaryMatching.ResidualSearch
open Finset
variable {n : ℕ}
abbrev Table (n : ℕ) := Fin n → Option (List (Fin n))

def initial (a : Fin n) : Table n := fun v => if v=a then some [a] else none

def predecessor (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (v : Fin n) : Option (Fin n) :=
  (List.finRange n).find? (fun u => decide (R u v) && (p u).isSome)

def step (R : Fin n → Fin n → Prop) [DecidableRel R] (p : Table n) : Table n :=
  fun v => match p v with
  | some l => some l
  | none => match predecessor R p v with
    | none => none
    | some u => (p u).map (fun l => v::l)

def search (R : Fin n → Fin n → Prop) [DecidableRel R] (a : Fin n) : ℕ → Table n
  | 0 => initial a
  | k+1 => step R (search R a k)

def reached (p : Table n) : Finset (Fin n) := univ.filter (fun v => (p v).isSome)

def Closed (R : Fin n → Fin n → Prop) (S : Finset (Fin n)) : Prop :=
  ∀ u ∈ S, ∀ v, R u v → v ∈ S

structure Good (R : Fin n → Fin n → Prop) (a : Fin n) (p : Table n) : Prop where
  head : ∀ v l, p v=some l → l.head?=some v
  last : ∀ v l, p v=some l → l.getLast?=some a
  simple : ∀ v l, p v=some l → l.Nodup
  chain : ∀ v l, p v=some l → l.IsChain (fun v u => R u v)
  visited : ∀ v l, p v=some l → ∀ u∈l, (p u).isSome

lemma mem_reached (p : Table n) (v : Fin n) : v∈reached p ↔ (p v).isSome := by
  simp [reached]

lemma predecessor_some (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (v u : Fin n) (h : predecessor R p v=some u) :
    R u v ∧ (p u).isSome := by
  have := List.find?_some h
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using this

lemma predecessor_exists (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (v : Fin n) :
    (predecessor R p v).isSome ↔ ∃ u, R u v ∧ (p u).isSome := by
  simp [predecessor, List.find?_isSome, Bool.and_eq_true]

lemma step_old (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (v : Fin n) (l : List (Fin n)) (h : p v=some l) :
    step R p v=some l := by simp [step, h]

lemma step_some (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (v : Fin n) (l : List (Fin n)) (h : step R p v=some l) :
    p v=some l ∨ (p v=none ∧ ∃ u t, p u=some t ∧ R u v ∧ l=v::t) := by
  unfold step at h
  cases he : p v with
  | some t => simp only [he] at h; exact Or.inl h
  | none =>
    simp only [he] at h
    cases hu : predecessor R p v with
    | none => simp [hu] at h
    | some u =>
      have hh := predecessor_some R p v u hu
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hh.2
      simp [hu, ht] at h
      exact Or.inr ⟨rfl, u, t, ht, hh.1, h.symm⟩

lemma step_reached (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (v : Fin n) :
    v∈reached (step R p) ↔ v∈reached p ∨ ∃ u∈reached p, R u v := by
  simp only [mem_reached]
  constructor
  · intro h
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp h
    rcases step_some R p v l hl with ho | ⟨_,u,t,ht,hr,_⟩
    · exact Or.inl (by simp [ho])
    · exact Or.inr ⟨u, by simp [ht], hr⟩
  · rintro (ho | ⟨u,hu,hr⟩)
    · obtain ⟨l,hl⟩ := Option.isSome_iff_exists.mp ho
      simp [step_old R p v l hl]
    · cases hv : p v with
      | some l => simp [step_old R p v l hv]
      | none =>
        have hh : (predecessor R p v).isSome := (predecessor_exists R p v).2 ⟨u,hr,hu⟩
        obtain ⟨w,hw⟩ := Option.isSome_iff_exists.mp hh
        obtain ⟨l,hl⟩ := Option.isSome_iff_exists.mp (predecessor_some R p v w hw).2
        simp [step,hv,hw,hl]

lemma reached_mono (R : Fin n → Fin n → Prop) [DecidableRel R] (p : Table n) :
    reached p ⊆ reached (step R p) := fun v hv => (step_reached R p v).2 (Or.inl hv)

lemma good_initial (R : Fin n → Fin n → Prop) (a : Fin n) : Good R a (initial a) := by
  constructor
  all_goals intro v l h; by_cases hv : v=a
  all_goals simp [initial,hv] at h
  all_goals subst v; subst l
  · rfl
  · rfl
  · simp
  · simp
  · intro u hu; simpa [initial] using hu

lemma good_step (R : Fin n → Fin n → Prop) [DecidableRel R]
    (a : Fin n) (p : Table n) (hp : Good R a p) : Good R a (step R p) := by
  have hpaths : ∀ v l, step R p v=some l →
      l.head?=some v ∧ l.getLast?=some a ∧ l.Nodup ∧
      l.IsChain (fun v u => R u v) ∧ ∀ u∈l, (step R p u).isSome := by
    intro v l hl
    rcases step_some R p v l hl with ho | ⟨hv,u,t,ht,hr,hlt⟩
    · refine ⟨hp.head v l ho, hp.last v l ho, hp.simple v l ho, hp.chain v l ho, ?_⟩
      intro u hu
      exact (mem_reached _ _).mp (reached_mono R p ((mem_reached _ _).mpr (hp.visited v l ho u hu)))
    · subst l
      have hvnot : v∉t := by
        intro hh
        have hhv := hp.visited u t ht v hh
        simp [hv] at hhv
      have htnon : t≠[] := by
        intro hnil
        have hh := hp.head u t ht
        simp [hnil] at hh
      refine ⟨rfl, ?_, (hp.simple u t ht).cons hvnot, ?_, ?_⟩
      · cases t with
        | nil => exact (htnon rfl).elim
        | cons w t => simpa only [List.getLast?_cons_cons] using hp.last u (w::t) ht
      · apply (hp.chain u t ht).cons
        intro w hw
        rw [hp.head u t ht] at hw
        simp only [Option.mem_some_iff] at hw
        subst w
        exact hr
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hwt
        · simp [hl]
        · exact (mem_reached _ _).mp (reached_mono R p
            ((mem_reached _ _).mpr (hp.visited u t ht w hwt)))
  exact ⟨fun v l h => (hpaths v l h).1, fun v l h => (hpaths v l h).2.1,
    fun v l h => (hpaths v l h).2.2.1, fun v l h => (hpaths v l h).2.2.2.1,
    fun v l h => (hpaths v l h).2.2.2.2⟩

lemma good_search (R : Fin n → Fin n → Prop) [DecidableRel R] (a : Fin n) (k : ℕ) :
    Good R a (search R a k) := by
  induction k with
  | zero => exact good_initial R a
  | succ k ih => exact good_step R a _ ih

lemma closed_step_eq (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (hc : Closed R (reached p)) : reached (step R p) = reached p := by
  ext v
  rw [step_reached]
  constructor
  · rintro (h | ⟨u,hu,hr⟩)
    · exact h
    · exact hc u hu v hr
  · exact Or.inl

lemma closed_step (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (hc : Closed R (reached p)) : Closed R (reached (step R p)) := by
  rw [closed_step_eq R p hc]
  exact hc

lemma card_increases (R : Fin n → Fin n → Prop) [DecidableRel R]
    (p : Table n) (hc : ¬Closed R (reached p)) :
    (reached p).card < (reached (step R p)).card := by
  apply card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨reached_mono R p, ?_⟩
  intro heq
  apply hc
  intro u hu v hr
  rw [heq]
  exact (step_reached R p v).2 (Or.inr ⟨u, hu, hr⟩)

lemma closed_or_card (R : Fin n → Fin n → Prop) [DecidableRel R]
    (a : Fin n) (k : ℕ) :
    Closed R (reached (search R a k)) ∨ k+1 ≤ (reached (search R a k)).card := by
  induction k with
  | zero =>
    right
    apply card_pos.mpr
    refine ⟨a, ?_⟩
    simp [search,mem_reached,initial]
  | succ k ih =>
    by_cases hc : Closed R (reached (search R a k))
    · exact Or.inl (closed_step R _ hc)
    · have hh := ih.resolve_left hc
      have hlt := card_increases R _ hc
      right
      change k+1+1 ≤ (reached (step R (search R a k))).card
      omega

lemma search_closed (R : Fin n → Fin n → Prop) [DecidableRel R] (a : Fin n) :
    Closed R (reached (search R a n)) := by
  rcases closed_or_card R a n with h | h
  · exact h
  · have hc := card_le_univ (reached (search R a n))
    simp only [Fintype.card_fin] at hc
    omega

lemma source_reached (R : Fin n → Fin n → Prop) [DecidableRel R] (a : Fin n) (k : ℕ) :
    a ∈ reached (search R a k) := by
  induction k with
  | zero => simp [search,mem_reached,initial]
  | succ k ih => exact reached_mono R _ ih

lemma search_path (R : Fin n → Fin n → Prop) [DecidableRel R]
    (a z : Fin n) (p : List (Fin n)) (hp : search R a n z = some p) :
    p.head?=some z ∧ p.getLast?=some a ∧ p.Nodup ∧
      p.IsChain (fun v u => R u v) := by
  have h := good_search R a n
  exact ⟨h.head z p hp, h.last z p hp, h.simple z p hp, h.chain z p hp⟩

lemma search_no_path (R : Fin n → Fin n → Prop) [DecidableRel R]
    (a z : Fin n) (hp : search R a n z = none) :
    a∈reached (search R a n) ∧ z∉reached (search R a n) ∧
      Closed R (reached (search R a n)) := by
  exact ⟨source_reached R a n, by simp [mem_reached,hp], search_closed R a⟩

end BinaryMatching.ResidualSearch
end

end OAI
