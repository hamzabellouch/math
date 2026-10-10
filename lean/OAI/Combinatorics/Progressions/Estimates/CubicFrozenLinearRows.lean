import OAI.Combinatorics.Progressions.Estimates.CubicPermutedSeven

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_cubic_hhn_row_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p) (h : ℤ)
      (k : Fin W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 1 ((p + C) ^ C)
        (fun x => W.eval k (cubicTrilinearInput h h (x ())))) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_frozen_affine_expansion (fun _ : CubicReplicatedIndex => 1)
  refine ⟨C, hC, ?_⟩
  intro p W h k
  classical
  let S : Finset CubicReplicatedIndex := {cubicRightReplica}
  let A : CubicReplicatedIndex → ℤ := fun j => if j = cubicRightReplica then 1 else 0
  let b : CubicReplicatedIndex → ℤ := fun j => if j = cubicRightReplica then 0 else h
  have hA : ∀ j, j ∉ S → A j = 0 := by
    intro j hj
    exact ite_eq_right (by simpa only [S, Finset.mem_singleton] using hj)
  obtain ⟨E, _⟩ := hfreeze W S A b k hA
  have hdegree : (∑ i ∈ S, (fun _ : CubicReplicatedIndex => 1) i) = 1 := by simp [S]
  have hin (x : Unit → ℤ) : (fun j => b j + A j * x ()) = cubicTrilinearInput h h (x ()) := by
    funext j
    rcases j with ⟨j, l⟩
    fin_cases j <;> fin_cases l <;> simp [A, b, cubicRightReplica, cubicTrilinearInput]
  have heq : (fun x : Unit → ℤ => W.eval k (fun j => b j + A j * x ())) =
      (fun x => W.eval k (cubicTrilinearInput h h (x ()))) := by
    funext x
    rw [hin]
  rw [hdegree, heq] at E
  exact ⟨E⟩

theorem exists_cubicHhnTensor_row_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p) (h : ℤ)
      (a : Fin 3 → Fin W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 1 ((p + C) ^ C)
        (fun x => W.cubicHhnTensor a ![h, x ()])) := by
  obtain ⟨A, _, hrow⟩ := exists_cubic_hhn_row_expansion
  obtain ⟨B, _, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget 3
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W h a
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨F⟩ := hprod (fun i (x : Unit → ℤ) => W.eval (a i) (cubicTrilinearInput h h (x ())))
    (by positivity : 0 ≤ (p + A) ^ A) (fun i => hrow W h (a i))
  have hcost : ((p + A) ^ A + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨F.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
