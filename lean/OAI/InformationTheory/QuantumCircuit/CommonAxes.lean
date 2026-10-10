import OAI.InformationTheory.QuantumCircuit.RegularApproximation

namespace OAI

/-! Product counts sharing the same local axes. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace QAC

lemma jointTest_subcount_of {N : ℕ} (l : List (Count N)) (M : Count N)
    (h : ∀ A ∈ l, A.Subcount M) : (jointTest l).Subcount M := by
  induction l with
  | nil => exact ⟨Finset.empty_subset _, by simp [jointTest, Count.empty]⟩
  | cons A l ih =>
      exact (h A (List.mem_cons_self ..)).join
        (ih (fun B hb => h B (List.mem_cons_of_mem _ hb)))

lemma Count.compatible_zero_pattern_commute {N : ℕ} (A B : Count N)
    (h : ∀ i ∈ A.support, i ∈ B.support → A.vector i = B.vector i)
    (F : Finset (Fin N)) : Commute A.zero (B.pattern F) := by
  classical
  change A.zero * B.pattern F = B.pattern F * A.zero
  unfold Count.zero Count.pattern
  rw [tensorMatrix_mul, tensorMatrix_mul]
  congr 1
  funext i
  by_cases ha : i ∈ A.support
  · by_cases hb : i ∈ B.support
    · by_cases hf : i ∈ F <;> simp [ha, hb, hf, h i ha hb, mul_sub, sub_mul]
    · simp [ha, hb]
  · simp [ha]

lemma Count.compatible_zero_high_commute {N : ℕ} (A B : Count N)
    (h : ∀ i ∈ A.support, i ∈ B.support → A.vector i = B.vector i)
    (r : ℝ) : Commute A.zero (B.high r) := by
  classical
  change A.zero * B.high r = B.high r * A.zero
  rw [Count.high, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro F _
  split_ifs
  · exact (A.compatible_zero_pattern_commute B h F).eq
  · simp

lemma reflection_joint_high_commute {N : ℕ} (R : ReflectionLayer N)
    (S : List (Count N)) (hS : S.Sublist R.gates) (r : ℝ) :
    Commute (reflectionMatrix R) ((jointTest S).high r) := by
  rw [reflectionMatrix_eq]
  apply Commute.list_prod_left
  intro x hx
  obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hx
  have hA' := jointTest_subcount R.gates R.disjoint A hA
  have hB' := jointTest_subcount_of S (jointTest R.gates)
    (fun B hB => jointTest_subcount R.gates R.disjoint B (hS.subset hB))
  exact (Commute.one_left _).sub_left
    ((A.compatible_zero_high_commute _ (fun i hi hj =>
      (hA'.2 i hi).trans (hB'.2 i hj).symm) r).smul_left (2 : ℝ))

lemma reflection_joint_tail_eq {N : ℕ} (R : ReflectionLayer N)
    (S : List (Count N)) (hS : S.Sublist R.gates) (r : ℝ) (ψ : State N) :
    ‖act ((jointTest S).high r) (act (reflectionMatrix R) ψ)‖ =
      ‖act ((jointTest S).high r) ψ‖ := by
  rw [← act_mul, ← (reflection_joint_high_commute R S hS r).eq, act_mul]
  exact act_unitary_norm (reflectionMatrix_unitary R) _

end QAC

end

end OAI
