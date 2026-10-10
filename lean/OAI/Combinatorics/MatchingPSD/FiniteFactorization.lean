import OAI.Combinatorics.MatchingPSD.CellLowerBound

namespace OAI

universe u_1 u_2

namespace PerfectMatchingPSD

lemma endpoint_count {n : ℕ} (U : Finset (Fin n)) (M : PerfectMatching n) :
    (∑ e ∈ M.1, ((if e.1.1 ∈ U then 1 else 0) +
      (if e.1.2 ∈ U then 1 else 0) : ℕ)) = U.card := by
  classical
  have pair_count (e : Edge n) :
      (∑ v ∈ U, (if e.1.1 = v ∨ e.1.2 = v then 1 else 0 : ℕ)) =
        (if e.1.1 ∈ U then 1 else 0) + (if e.1.2 ∈ U then 1 else 0) := by
    have pointwise (v : Fin n) :
        (if e.1.1 = v ∨ e.1.2 = v then 1 else 0 : ℕ) =
          (if e.1.1 = v then 1 else 0) + (if e.1.2 = v then 1 else 0) := by
      have hne : e.1.1 ≠ e.1.2 := ne_of_lt e.2
      by_cases h₁ : e.1.1 = v <;> by_cases h₂ : e.1.2 = v <;> simp_all
    simp_rw [pointwise]
    simp [Finset.sum_add_distrib]
  calc
    _ = ∑ e ∈ M.1, ∑ v ∈ U,
        (if e.1.1 = v ∨ e.1.2 = v then 1 else 0 : ℕ) := by
      apply Finset.sum_congr rfl
      intro e _
      exact (pair_count e).symm
    _ = ∑ v ∈ U, ∑ e ∈ M.1,
        (if e.1.1 = v ∨ e.1.2 = v then 1 else 0 : ℕ) := Finset.sum_comm
    _ = ∑ v ∈ U, (M.1.filter fun e => e.1.1 = v ∨ e.1.2 = v).card := by
      simp only [Finset.sum_boole, Nat.cast_id]
    _ = U.card := by
      have hm : ∀ v : Fin n,
          (M.1.filter fun e => e.1.1 = v ∨ e.1.2 = v).card = 1 := M.2
      simp [hm]

lemma cut_degree_identity {n : ℕ} (U : Finset (Fin n)) (M : PerfectMatching n) :
    U.card = 2 * (M.1.filter fun e => e.1.1 ∈ U ∧ e.1.2 ∈ U).card +
      crossingCount U M := by
  classical
  rw [← endpoint_count U M]
  have term (e : Edge n) :
      ((if e.1.1 ∈ U then 1 else 0) + (if e.1.2 ∈ U then 1 else 0) : ℕ) =
        2 * (if e.1.1 ∈ U ∧ e.1.2 ∈ U then 1 else 0) +
          (if Crosses U e then 1 else 0) := by
    by_cases h₁ : e.1.1 ∈ U <;> by_cases h₂ : e.1.2 ∈ U <;>
      simp [h₁, h₂, Crosses]
  simp_rw [term]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_boole, Nat.cast_id, crossingCount]

lemma crossingCount_pos {n : ℕ} (U : OddCut n) (M : PerfectMatching n) :
    0 < crossingCount U.1 M := by
  obtain ⟨k, hk⟩ := U.2
  have h := cut_degree_identity U.1 M
  omega

lemma slack_nonneg {n : ℕ} (i : Row n) (M : PerfectMatching n) :
    0 ≤ slack i M := by
  classical
  rcases i with e | U
  · simp only [slack]
    split_ifs <;> norm_num
  · have h : 1 ≤ crossingCount U.1 M := crossingCount_pos U M
    have hr : (1 : ℝ) ≤ (crossingCount U.1 M : ℝ) := by exact_mod_cast h
    simpa only [slack, sub_nonneg] using hr

lemma exists_diagonal_factorization {I : Type u_1} {J : Type u_2} [Finite J]
    (S : I → J → ℝ) (hS : ∀ i j, 0 ≤ S i j) :
    ∃ r : ℕ, 0 < r ∧
      ∃ (A : I → Matrix (Fin r) (Fin r) ℝ)
        (B : J → Matrix (Fin r) (Fin r) ℝ),
        (∀ i, (A i).PosSemidef) ∧ (∀ j, (B j).PosSemidef) ∧
        ∀ i j, S i j = Matrix.trace (A i * B j) := by
  classical
  let : Fintype J := Fintype.ofFinite J
  let e := Fintype.equivFin (Option J)
  let a (i : I) (k : Option J) : ℝ := k.elim 0 (S i)
  let b (j : J) (k : Option J) : ℝ := if k = some j then 1 else 0
  refine ⟨Fintype.card (Option J), by simp,
    (fun i => (Matrix.diagonal (a i)).submatrix e.symm e.symm),
    (fun j => (Matrix.diagonal (b j)).submatrix e.symm e.symm), ?_, ?_, ?_⟩
  · intro i
    apply Matrix.PosSemidef.submatrix
    apply Matrix.PosSemidef.diagonal
    intro k
    cases k with
    | none => exact le_rfl
    | some j => exact hS i j
  · intro j
    apply Matrix.PosSemidef.submatrix
    apply Matrix.PosSemidef.diagonal
    intro k
    dsimp [b]
    split_ifs <;> norm_num
  · intro i j
    rw [Matrix.submatrix_mul_equiv, Matrix.diagonal_mul_diagonal,
      Matrix.submatrix_diagonal _ _ e.symm.injective, Matrix.trace_diagonal]
    dsimp only [Function.comp_def]
    rw [e.symm.sum_comp (fun k => a i k * b j k)]
    simp [a, b]

lemma factor_orders_nonempty (n : ℕ) :
    {r : ℕ | 0 < r ∧ HasFactorization n r}.Nonempty := by
  obtain ⟨r, hr, h⟩ := exists_diagonal_factorization (@slack n) slack_nonneg
  exact ⟨r, hr, h⟩

lemma psdRank_pos (n : ℕ) : 0 < psdRank n :=
  (Nat.sInf_mem (factor_orders_nonempty n)).1

lemma hasFactorization_psdRank (n : ℕ) : HasFactorization n (psdRank n) :=
  (Nat.sInf_mem (factor_orders_nonempty n)).2

lemma psdRank_le {n r : ℕ} (hr : 0 < r) (h : HasFactorization n r) :
    psdRank n ≤ r := Nat.sInf_le ⟨hr, h⟩

end PerfectMatchingPSD

end OAI
