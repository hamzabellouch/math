import Mathlib

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
variable {N : ℕ}

def nearestEndpoint (r : ℚ) : ℚ := if 0≤r then 1 else -1

def freezeOne (σ : ℚ) (x : Fin N → ℚ) (i : Fin N) : Fin N → ℚ :=
  if 1-|x i|≤σ then Function.update x i (nearestEndpoint (x i)) else x

def freezeList (σ : ℚ) : (Fin N → ℚ) → List (Fin N) → (Fin N → ℚ)
  | x,[] => x
  | x,i::is => freezeList σ (freezeOne σ x i) is

def freezeAll (σ : ℚ) (x : Fin N → ℚ) : Fin N → ℚ := freezeList σ x (List.finRange N)

lemma nearestEndpoint_abs (r : ℚ) : |nearestEndpoint r|=1 := by
  unfold nearestEndpoint
  split <;> norm_num

lemma nearestEndpoint_dist {r : ℚ} (hr : |r|≤1) : |nearestEndpoint r-r|=1-|r| := by
  unfold nearestEndpoint
  split
  · rename_i h
    rw [abs_of_nonneg h,abs_of_nonneg (by linarith [(abs_le.mp hr).2])]
  · rename_i h
    have hn : r≤0 := (lt_of_not_ge h).le
    rw [abs_of_nonpos hn,abs_of_nonpos (by linarith [(abs_le.mp hr).1])]
    ring

lemma freezeOne_cube (σ : ℚ) (x : Fin N → ℚ) (hx : ∀ i,|x i|≤1) (i : Fin N) :
    ∀ j,|freezeOne σ x i j|≤1 := by
  unfold freezeOne
  split
  · intro j
    by_cases hj : j=i
    · subst j;simpa using (nearestEndpoint_abs (x i)).le
    · simpa only [Function.update_of_ne hj] using hx j
  · exact hx

lemma freezeOne_other (σ : ℚ) (x : Fin N → ℚ) (i j : Fin N) (hji : j≠i) :
    freezeOne σ x i j=x j := by
  unfold freezeOne
  split <;> simp [Function.update_of_ne hji]

lemma freezeOne_assigned (σ : ℚ) (x : Fin N → ℚ) (i : Fin N) :
    |freezeOne σ x i i|=1 ∨ σ<1-|freezeOne σ x i i| := by
  unfold freezeOne
  split
  · exact Or.inl (by simpa using nearestEndpoint_abs (x i))
  · exact Or.inr (lt_of_not_ge ‹¬1-|x i|≤σ›)

lemma freezeOne_preserves_assigned (σ : ℚ) (x : Fin N → ℚ) (i j : Fin N)
    (h : |x j|=1 ∨ σ<1-|x j|) :
    |freezeOne σ x i j|=1 ∨ σ<1-|freezeOne σ x i j| := by
  by_cases hji : j=i
  · subst j;exact freezeOne_assigned σ x i
  · simpa only [freezeOne_other σ x i j hji] using h

lemma freezeList_cube (σ : ℚ) (x : Fin N → ℚ) (hx : ∀ i,|x i|≤1) (l : List (Fin N)) :
    ∀ j,|freezeList σ x l j|≤1 := by
  induction l generalizing x with
  | nil => exact hx
  | cons i is ih => exact ih _ (freezeOne_cube σ x hx i)

lemma freezeList_preserves_assigned (σ : ℚ) (x : Fin N → ℚ) (l : List (Fin N)) (j : Fin N)
    (h : |x j|=1 ∨ σ<1-|x j|) :
    |freezeList σ x l j|=1 ∨ σ<1-|freezeList σ x l j| := by
  induction l generalizing x with
  | nil => exact h
  | cons i is ih => exact ih _ (freezeOne_preserves_assigned σ x i j h)

lemma freezeList_assigned (σ : ℚ) (x : Fin N → ℚ) (l : List (Fin N)) (j : Fin N) (hj : j∈l) :
    |freezeList σ x l j|=1 ∨ σ<1-|freezeList σ x l j| := by
  induction l generalizing x with
  | nil => simp at hj
  | cons i is ih =>
    rcases List.mem_cons.mp hj with hij|hj
    · subst j
      exact freezeList_preserves_assigned σ _ is i (freezeOne_assigned σ x i)
    · exact ih _ hj

lemma freezeAll_strip (σ : ℚ) (x : Fin N → ℚ) (j : Fin N)
    (hj : |freezeAll σ x j|<1) : |freezeAll σ x j|<1-σ := by
  have hh := freezeList_assigned σ x (List.finRange N) j (List.mem_finRange j)
  change |freezeAll σ x j|=1 ∨ σ<1-|freezeAll σ x j| at hh
  rcases hh with h|h <;> linarith

end CurrentKS.RationalFace

end OAI
