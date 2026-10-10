import OAI.Analysis.Laughlin.Fock.Coordinates

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem sum_unoccupied_insert {Q : ℕ} {R : Type*} [AddCommMonoid R]
    (i : Fin (Q+1)) (f : Finset (Fin (Q+1)) → R) :
    (∑ A ∈ Finset.univ.filter (fun A : Finset (Fin (Q+1)) => i ∉ A), f (insert i A)) =
      ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin (Q+1)) => i ∈ A), f A := by
  classical
  apply Finset.sum_bij (fun A _ => insert i A)
  · intro A hA
    simp
  · intro A hA B hB h
    have ha := (Finset.mem_filter.mp hA).2
    have hb := (Finset.mem_filter.mp hB).2
    have he := congrArg (fun C => C.erase i) h
    simpa [Finset.erase_insert,ha,hb] using he
  · intro B hB
    have hb := (Finset.mem_filter.mp hB).2
    exact ⟨B.erase i,by simp,Finset.insert_erase hb⟩
  · intro A hA
    rfl

theorem annihilate_normSq (Q : ℕ) (i : Fin (Q+1)) (x : Space Q) :
    occupationNormSq Q (annihilate i x) =
      ∑ A : Finset (Fin (Q+1)), if i ∈ A then ‖(occupationBasis Q).repr x A‖^2 else 0 := by
  have h (A : Finset (Fin (Q+1))) :
      ‖(occupationBasis Q).repr (annihilate i x) A‖^2 =
        if i ∉ A then ‖(occupationBasis Q).repr x (insert i A)‖^2 else 0 := by
    by_cases hi : i ∈ A <;> simp [annihilate_coordinate,hi,insertionSign_norm]
  unfold occupationNormSq
  simp_rw [h]
  simpa only [Finset.sum_filter] using
    sum_unoccupied_insert (R := ℝ) i (fun A => ‖(occupationBasis Q).repr x A‖^2)

theorem annihilate_normSq_le (Q : ℕ) (i : Fin (Q+1)) (x : Space Q) :
    occupationNormSq Q (annihilate i x) ≤ occupationNormSq Q x := by
  rw [annihilate_normSq]
  unfold occupationNormSq
  apply Finset.sum_le_sum
  intro A hA
  split_ifs
  · exact le_rfl
  · positivity

theorem two_annihilate_normSq_le (Q : ℕ) (j k : Fin (Q+1)) (x : Space Q) :
    occupationNormSq Q (annihilate k (annihilate j x)) ≤ occupationNormSq Q x :=
  (annihilate_normSq_le Q k _).trans (annihilate_normSq_le Q j x)

theorem sourceFour_normSq_le_pair (Q p : ℕ) (j k : Fin (Q+1)) (x : Space Q) :
    occupationNormSq Q (sourceFourEnd Q p j k x) ≤
      occupationNormSq Q (sourcePairEnd Q p x) :=
  two_annihilate_normSq_le Q j k (sourcePairEnd Q p x)

theorem limitFour_normSq_le_pair (Q p : ℕ) (j k : Fin (Q+1)) (x : Space Q) :
    occupationNormSq Q (limitFourEnd Q p j k x) ≤
      occupationNormSq Q (limitPairEnd Q p x) :=
  two_annihilate_normSq_le Q j k (limitPairEnd Q p x)

end Laughlin.Fock

end OAI
