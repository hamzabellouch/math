import OAI.Combinatorics.ContingencyTables.Dense.DenseExponentListProgram
import OAI.Combinatorics.MatchingCount.Machines.TreeIndex

namespace OAI

/-! # Computing a maximal margin in binary -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped

def maximumIndex (xs : List ℕ) : ℕ := xs.idxOf (listMaximum (xs,0))

def maximumIndexRealizer : Realizer maximumIndex :=
  composition (pair (composition (pair identity (constant 0)) listMaximumRealizer) identity)
    (indexOf natEqual)

theorem polynomial_maximumIndex : PolynomialTime maximumIndexRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant 0))
      polynomial_listMaximum) polynomial_identity) (polynomial_indexOf polynomial_natEqual)

lemma listMaximum_mem_or_default (xs : List ℕ) (a : ℕ) :
    listMaximum (xs,a)=a ∨ listMaximum (xs,a)∈xs := by
  induction xs generalizing a with
  | nil => exact Or.inl rfl
  | cons b bs ih =>
    change listMaximum (bs,max b a)=a ∨ listMaximum (bs,max b a)∈b::bs
    rcases ih (max b a) with he|hm
    · rw [he]
      rcases le_total b a with h|h
      · exact Or.inl (max_eq_right h)
      · exact Or.inr (by simp [max_eq_left h])
    · exact Or.inr (List.mem_cons_of_mem b hm)

lemma listMaximum_mem (xs : List ℕ) (hx : xs≠[]) : listMaximum (xs,0)∈xs := by
  cases xs with
  | nil => exact (hx rfl).elim
  | cons a xs =>
    change listMaximum (xs,max a 0)∈a::xs
    rw [Nat.max_zero]
    rcases listMaximum_mem_or_default xs a with he|hm
    · simp [he]
    · exact List.mem_cons_of_mem a hm

theorem maximumIndex_lt (xs : List ℕ) (hx : xs≠[]) : maximumIndex xs < xs.length :=
  List.idxOf_lt_length_iff.mpr (listMaximum_mem xs hx)

theorem maximumIndex_value (xs : List ℕ) (hx : xs≠[]) :
    xs.getD (maximumIndex xs) 0=listMaximum (xs,0) := by
  rw [List.getD_eq_getElem xs 0 (maximumIndex_lt xs hx)]
  exact List.getElem_idxOf (maximumIndex_lt xs hx)

theorem maximumIndex_maximal (xs : List ℕ) (hx : xs≠[]) (a : ℕ) (ha : a∈xs) :
    a≤xs.getD (maximumIndex xs) 0 := by
  rw [maximumIndex_value xs hx]
  exact le_listMaximum_member xs 0 a ha

def maximumPosition {n : ℕ} (f : Fin (n+1) → ℕ) : Fin (n+1) :=
  ⟨maximumIndex (List.ofFn f),by
    simpa only [List.length_ofFn] using maximumIndex_lt (List.ofFn f)
      (by intro h; have := congrArg List.length h; simp only [List.length_ofFn,List.length_nil] at this; omega)⟩

theorem maximumPosition_spec {n : ℕ} (f : Fin (n+1) → ℕ) (i : Fin (n+1)) :
    f i≤f (maximumPosition f) := by
  have hx : List.ofFn f≠[] := by
    intro h
    have := congrArg List.length h
    simp only [List.length_ofFn,List.length_nil] at this
    omega
  have hm := maximumIndex_maximal (List.ofFn f) hx (f i) (List.mem_ofFn.mpr ⟨i,rfl⟩)
  have he : (List.ofFn f).getD (maximumIndex (List.ofFn f)) 0=f (maximumPosition f) := by
    rw [List.getD_eq_getElem (List.ofFn f) 0 (maximumIndex_lt (List.ofFn f) hx),List.getElem_ofFn]
    rfl
  rwa [he] at hm

end ContingencyTables.DensePrograms

end OAI
