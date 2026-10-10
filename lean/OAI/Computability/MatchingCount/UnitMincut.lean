import OAI.Computability.MatchingCount.ResidualSearch

namespace OAI

section

namespace BinaryMatching.UnitMincut
open Finset UnitFlow ResidualSearch
variable {n : ℕ}

def residual (c : Fin n → Fin n → ℕ) (b : Matrix (Fin n)) : Fin n → Fin n → Prop :=
  fun i j => b i j < c i j
instance residualDecidable (c : Fin n → Fin n → ℕ) (b : Matrix (Fin n)) :
    DecidableRel (residual c b) := fun _ _ => inferInstanceAs (Decidable (_ < (_ : ℤ)))

def augment (c : Fin n → Fin n → ℕ) (a z : Fin n) (b : Matrix (Fin n)) : Matrix (Fin n) :=
  match search (residual c b) a n z with
  | none => b
  | some p => fun i j => b i j + pathFlow p i j

def iterate (c : Fin n → Fin n → ℕ) (a z : Fin n) : ℕ → Matrix (Fin n)
  | 0 => fun _ _ => 0
  | k+1 => augment c a z (iterate c a z k)

def sourceCapacity (c : Fin n → Fin n → ℕ) (a : Fin n) : ℕ := ∑ j, c a j

def mincut (c : Fin n → Fin n → ℕ) (a z : Fin n) : Finset (Fin n) :=
  let b := iterate c a z (sourceCapacity c a)
  reached (search (residual c b) a n)

lemma augment_of_none (c : Fin n → Fin n → ℕ) (a z : Fin n) (b : Matrix (Fin n))
    (h : search (residual c b) a n z=none) : augment c a z b=b := by
  simp [augment,h]

lemma augment_of_some (c : Fin n → Fin n → ℕ) (a z : Fin n) (b : Matrix (Fin n))
    (p : List (Fin n)) (h : search (residual c b) a n z=some p) :
    augment c a z b = (fun i j => b i j + pathFlow p i j) := by
  simp [augment,h]

lemma augment_preserves (c : Fin n → Fin n → ℕ) (a z : Fin n) (b : Matrix (Fin n))
    (hb : Feasible c a z b) : Feasible c a z (augment c a z b) := by
  cases he : search (residual c b) a n z with
  | none => rwa [augment_of_none c a z b he]
  | some p =>
    rw [augment_of_some c a z b p he]
    obtain ⟨hhead,hlast,hnd,hchain⟩ := search_path (residual c b) a z p he
    exact augment_feasible hb p hnd hchain hhead hlast

lemma iterate_feasible (c : Fin n → Fin n → ℕ) (a z : Fin n) (k : ℕ) :
    Feasible c a z (iterate c a z k) := by
  induction k with
  | zero => exact feasible_zero c a z
  | succ k ih => exact augment_preserves c a z _ ih

lemma iterate_none_or_value (c : Fin n → Fin n → ℕ) (a z : Fin n) (haz : a≠z) (k : ℕ) :
    search (residual c (iterate c a z k)) a n z=none ∨
      divergence (iterate c a z k) a = k := by
  induction k with
  | zero => exact Or.inr (by simp [iterate,divergence])
  | succ k ih =>
    cases he : search (residual c (iterate c a z k)) a n z with
    | none =>
      left
      rwa [iterate,augment_of_none c a z _ he]
    | some p =>
      have hv := ih.resolve_left (by simp [he])
      right
      rw [iterate,augment_of_some c a z _ p he]
      obtain ⟨hhead,hlast,_,_⟩ := search_path (residual c (iterate c a z k)) a z p he
      rw [augment_value haz _ p hhead hlast,hv]
      simp

lemma final_no_path (c : Fin n → Fin n → ℕ) (a z : Fin n) (haz : a≠z) :
    search (residual c (iterate c a z (sourceCapacity c a))) a n z=none := by
  rcases iterate_none_or_value c a z haz (sourceCapacity c a) with h | h
  · exact h
  · cases he : search (residual c (iterate c a z (sourceCapacity c a))) a n z with
    | none => rfl
    | some p =>
      have hfeas := iterate_feasible c a z (sourceCapacity c a + 1)
      have hbound := source_bound hfeas
      rw [iterate,augment_of_some c a z _ p he] at hbound
      obtain ⟨hhead,hlast,_,_⟩ :=
        search_path (residual c (iterate c a z (sourceCapacity c a))) a z p he
      rw [augment_value haz _ p hhead hlast,h] at hbound
      have hc : (sourceCapacity c a : ℤ) = ∑ j, (c a j : ℤ) := by
        simp [sourceCapacity]
      rw [← hc] at hbound
      omega

theorem mincut_correct (c : Fin n → Fin n → ℕ) (a z : Fin n) (haz : a≠z) :
    a∈mincut c a z ∧ z∉mincut c a z ∧
      ∀ T : Finset (Fin n), a∈T → z∉T → cutCapacity c (mincut c a z) ≤ cutCapacity c T := by
  let b := iterate c a z (sourceCapacity c a)
  have hb : Feasible c a z b := iterate_feasible c a z _
  have hn : search (residual c b) a n z=none := final_no_path c a z haz
  obtain ⟨ha,hz,hclosed⟩ := search_no_path (residual c b) a z hn
  refine ⟨ha,hz,saturated_minimum hb _ ha hz ?_⟩
  intro i hi j hj
  apply le_antisymm (hb.capacity i j)
  by_contra hnot
  have hr : residual c b i j := lt_of_not_ge hnot
  exact hj (hclosed i hi j hr)

end BinaryMatching.UnitMincut
end

end OAI
