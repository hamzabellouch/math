import OAI.NumberTheory.Ostmann.Supply.BilinearCube

namespace OAI

/-! # Degree bounds the number of centered coordinates -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def cubeSupport {n : ℕ} (t : BilinearCube n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (t i).1 = true ∨ (t i).2 = true)

theorem cubeSupport_card_le {n : ℕ} (t : BilinearCube n) :
    (cubeSupport t).card ≤ cubeDegree t false + cubeDegree t true := by
  simp only [cubeSupport, Finset.card_eq_sum_ones, Finset.sum_filter, cubeDegree,
    Bool.false_eq_true, ite_false, ite_true, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  cases (t i).1 <;> cases (t i).2 <;> simp

theorem cubeProduct_eq_zero_of_many_coordinates {n : ℕ}
    (W : Fin n → Bool × Bool → ℂ) (Q : Finset (Fin n))
    (hW : ∀ i ∈ Q, W i (false, false) = 0) (t : BilinearCube n)
    (hQ : cubeDegree t false + cubeDegree t true < Q.card) :
    (∏ i, W i (t i)) = 0 := by
  have hnot : ¬ Q ⊆ cubeSupport t := by
    intro hsub
    exact (not_lt_of_ge ((Finset.card_le_card hsub).trans (cubeSupport_card_le t))) hQ
  obtain ⟨i, hi, hti⟩ := Finset.not_subset.mp hnot
  have ht : t i = (false, false) := by
    rcases hh : t i with ⟨a, b⟩
    cases a <;> cases b <;> simp_all [cubeSupport]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [ht]
  exact hW i hi

theorem cubeCoefficient_eq_zero_of_many_coordinates {n : ℕ}
    (W : Fin n → Bool × Bool → ℂ) (Q : Finset (Fin n))
    (hW : ∀ i ∈ Q, W i (false, false) = 0) (j k : ℕ) (hQ : j + k < Q.card) :
    cubeCoefficient (fun t => ∏ i, W i (t i)) j k = 0 := by
  unfold cubeCoefficient
  apply Finset.sum_eq_zero
  intro t ht
  have hd := (Finset.mem_filter.mp ht).2
  have h₁ : cubeDegree t false = j := congrArg Prod.fst hd
  have h₂ : cubeDegree t true = k := congrArg Prod.snd hd
  apply cubeProduct_eq_zero_of_many_coordinates W Q hW t
  simpa only [h₁, h₂] using hQ

end Ostmann

end OAI
