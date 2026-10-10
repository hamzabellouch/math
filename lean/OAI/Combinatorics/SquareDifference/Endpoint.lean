import OAI.Combinatorics.SquareDifference.PairBridge

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

def NatSquareFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ m : ℕ, 1 ≤ m → b ≠ a + m^2

noncomputable def natIndicator (A : Finset ℕ) (n : ℕ) : ℝ := if n∈A then 1 else 0

lemma natIndicator_bound (A : Finset ℕ) (n : ℕ) : |natIndicator A n|≤1 := by
  unfold natIndicator
  split_ifs <;> norm_num

lemma natIndicator_nonneg (A : Finset ℕ) (n : ℕ) : 0≤natIndicator A n := by
  unfold natIndicator
  split_ifs <;> norm_num

lemma natIndicator_vanish (N : ℕ) (A : Finset ℕ) (hA : A⊆range N) (n : ℕ) (hn : N≤n) :
    natIndicator A n=0 := by
  exact ite_eq_right (fun h => (Nat.not_lt.mpr hn) (mem_range.mp (hA h)))

lemma sum_natIndicator (N : ℕ) (A : Finset ℕ) (hA : A⊆range N) :
    (∑n∈range N,natIndicator A n)=(A.card:ℝ) := by
  unfold natIndicator
  rw [sum_boole]
  congr 1
  exact congrArg Finset.card (filter_mem_eq_inter.trans (inter_eq_right.mpr hA))

noncomputable def squareChild (A : Finset ℕ) (c D L : ℕ) : Finset ℕ :=
  (range L).filter (fun t => c+D^2*t∈A)

lemma squareChild_sub (A : Finset ℕ) (c D L : ℕ) : squareChild A c D L⊆range L := filter_subset _ _

lemma squareChild_free (A : Finset ℕ) (hA : NatSquareFree A) (c D L : ℕ) (hD : 0<D) :
    NatSquareFree (squareChild A c D L) := by
  intro a ha b hb m hm he
  have ha' := (mem_filter.mp ha).2
  have hb' := (mem_filter.mp hb).2
  apply hA _ ha' _ hb' (D*m) (by nlinarith)
  rw [he]
  ring

lemma squareChild_indicator (N : ℕ) (A : Finset ℕ) (hA : A⊆range N)
    (c D L : ℕ) (hNL : N≤D^2*L) (t : ℕ) :
    natIndicator (squareChild A c D L) t=natIndicator A (c+D^2*t) := by
  by_cases ht : t<L
  · simp only [natIndicator,squareChild,mem_filter,mem_range,ht,true_and]
  · have hn : N≤c+D^2*t := hNL.trans (by nlinarith [Nat.le_of_not_gt ht])
    rw [natIndicator_vanish N A hA _ hn]
    exact ite_eq_right (fun h => ht (mem_range.mp ((mem_filter.mp h).1)))

section Functional

variable {J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]

noncomputable def setFunctional (N Q : ℕ) (A : Finset ℕ) : ℝ :=
  diagonalIntegral (productTupleLaw p) (actualTruncatedLift p N Q (natIndicator A))

lemma setFunctional_nonneg (hp : ∀j,tupleReflectionThreshold≤(p j:ℝ)) (N Q : ℕ) (A : Finset ℕ) :
    0≤ setFunctional p N Q A := productTupleLaw_diagonal_nonneg p hp _

lemma setFunctional_density (hp : ∀j,max tupleMassThreshold tupleReflectionThreshold≤(p j:ℝ))
    (N Q : ℕ) (hQ : 1≤Q) (A : Finset ℕ) (hA : A⊆range N) :
    ((A.card:ℝ)/(N:ℝ))^(Fintype.card TupleVertex)≤ setFunctional p N Q A := by
  have hm := productTupleLaw_mean p hp (actualTruncatedLift p N Q (natIndicator A))
  rw [PairBridge.actualLift_mean p N Q hQ,sum_natIndicator N A hA] at hm
  have h0 : 0≤(A.card:ℝ)/(N:ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [show (N:ℝ)⁻¹*(A.card:ℝ)=(A.card:ℝ)/(N:ℝ) by ring,abs_of_nonneg h0] at hm
  have hh := pow_le_pow_left₀ h0 hm (Fintype.card TupleVertex)
  rw [diagonalRoot_pow _ (productTupleLaw_diagonal_nonneg p (fun j => (le_max_right _ _).trans (hp j)))] at hh
  exact hh

end Functional

end SquareDifference

end

end OAI
