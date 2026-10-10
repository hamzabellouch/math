import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralFiltrationAction

namespace OAI

/-! # Iterated action commutators and a centralizer criterion -/

namespace PolycyclicRecognition

open scoped commutatorElement
variable {G : Type} [Group G]

def relativeCommutatorSeries (K N : Subgroup G) : ℕ → Subgroup G
  | 0 => N
  | n + 1 => ⁅K, relativeCommutatorSeries K N n⁆

theorem relativeCommutatorSeries_mono (K : Subgroup G) {N M : Subgroup G}
    (h : N ≤ M) (n : ℕ) : relativeCommutatorSeries K N n ≤ relativeCommutatorSeries K M n := by
  induction n with
  | zero => exact h
  | succ n ih => exact Subgroup.commutator_mono_right ih

theorem relativeCommutatorSeries_antitone (K N : Subgroup G) [N.Normal] :
    Antitone (relativeCommutatorSeries K N) := by
  apply antitone_nat_of_succ_le
  intro n
  induction n with
  | zero => exact Subgroup.commutator_le_right K N
  | succ n ih => exact Subgroup.commutator_mono_right ih

theorem relativeCommutatorSeries_add (K N : Subgroup G) (i j : ℕ) :
    relativeCommutatorSeries K N (i + j) =
      relativeCommutatorSeries K (relativeCommutatorSeries K N i) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change ⁅K, relativeCommutatorSeries K N (i + j)⁆ =
      ⁅K, relativeCommutatorSeries K (relativeCommutatorSeries K N i) j⁆
    rw [ih]

instance relativeCommutatorSeries_normal (K N : Subgroup G) [K.Normal] [N.Normal] (n : ℕ) :
    (relativeCommutatorSeries K N n).Normal := by
  induction n with
  | zero => exact inferInstanceAs N.Normal
  | succ n ih =>
    let := ih
    exact inferInstanceAs (⁅K, relativeCommutatorSeries K N n⁆ : Subgroup G).Normal

theorem nilpotent_of_relativeCommutatorSeries (K N : Subgroup G) [K.Normal] [N.Normal]
    (c : ℕ) (hc : relativeCommutatorSeries K N c = ⊥)
    (hcent : Subgroup.centralizer (N : Set G) ≤ N) : Group.IsNilpotent K := by
  let U (i : ℕ) := relativeCommutatorSeries K N (c - i)
  refine nilpotent_of_central_filtration_action K U ?_ ?_ ?_ c ?_
  · intro i j hij
    exact relativeCommutatorSeries_antitone K N (Nat.sub_le_sub_left hij c)
  · simpa only [U, Nat.sub_zero] using hc
  · intro i
    by_cases hi : i < c
    · have he : c - i = (c - (i + 1)) + 1 := by omega
      change ⁅K, relativeCommutatorSeries K N (c - (i + 1))⁆ ≤
        relativeCommutatorSeries K N (c - i)
      rw [he]
      exact le_rfl
    · have hi' : c - i = 0 := Nat.sub_eq_zero_of_le (by omega)
      have hi'' : c - (i + 1) = 0 := Nat.sub_eq_zero_of_le (by omega)
      simpa only [U, hi', hi'', relativeCommutatorSeries] using
        Subgroup.commutator_le_right K N
  · simpa only [U, Nat.sub_self, relativeCommutatorSeries] using hcent

end PolycyclicRecognition

end OAI
