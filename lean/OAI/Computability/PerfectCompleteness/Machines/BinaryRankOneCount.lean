import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Rank
import OAI.Computability.PerfectCompleteness.Sampling.CutSamplerReplayTransportLemmas

namespace OAI

section

namespace PerfectCompleteness.BinaryRankOneCount

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

noncomputable section

theorem rank_le_one_iff_vecMulVec {K I J : Type*} [Field K]
    [Fintype I] [Fintype J] (A : Matrix I J K) :
    A.rank ≤ 1 ↔ ∃ u : I → K, ∃ v : J → K, Matrix.vecMulVec u v = A := by
  constructor
  · intro hA
    let S : Submodule K (I → K) := Submodule.span K (Set.range A.col)
    have hS : Module.finrank K S ≤ 1 := by
      simpa only [S, Matrix.rank_eq_finrank_span_cols] using hA
    obtain ⟨u, hu⟩ := (finrank_le_one_iff (K := K) (V := S)).mp hS
    have hcol (j : J) : A.col j ∈ S :=
      Submodule.subset_span (Set.mem_range_self j)
    choose v hv using (fun j : J => hu ⟨A.col j, hcol j⟩)
    refine ⟨u.val, v, ?_⟩
    ext i j
    change u.val i * v j = A i j
    have hij := congrArg (fun z : S => z.val i) (hv j)
    change v j * u.val i = A i j at hij
    exact (mul_comm _ _).trans hij
  · rintro ⟨u, v, rfl⟩
    exact Matrix.rank_vecMulVec_le u v

theorem rank_le_one_card_le_vec_pairs {K I J : Type*} [Field K]
    [Fintype K] [Fintype I] [Fintype J] :
    Fintype.card {A : Matrix I J K // A.rank ≤ 1} ≤
      Fintype.card ((I → K) × (J → K)) := by
  let outer : ((I → K) × (J → K)) → {A : Matrix I J K // A.rank ≤ 1} :=
    fun p => ⟨Matrix.vecMulVec p.1 p.2, Matrix.rank_vecMulVec_le p.1 p.2⟩
  apply Fintype.card_le_of_surjective outer
  intro A
  obtain ⟨u, v, huv⟩ := (rank_le_one_iff_vecMulVec A.val).mp A.property
  exact ⟨(u, v), Subtype.ext huv⟩

theorem binary_rank_le_one_card_le (m : Nat) :
    Fintype.card {A : Matrix (Fin m) (Fin m) (ZMod 2) // A.rank ≤ 1} ≤
      2 ^ (2 * m) := by
  let outer : ((Fin m → ZMod 2) × (Fin m → ZMod 2)) →
      {A : Matrix (Fin m) (Fin m) (ZMod 2) // A.rank ≤ 1} :=
    fun p => ⟨Matrix.vecMulVec p.1 p.2, Matrix.rank_vecMulVec_le p.1 p.2⟩
  have covers : Function.Surjective outer := by
    intro A
    obtain ⟨u, v, huv⟩ := (rank_le_one_iff_vecMulVec A.val).mp A.property
    exact ⟨(u, v), Subtype.ext huv⟩
  have vector_card : Fintype.card (Fin m → ZMod 2) = 2 ^ m := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  calc
    _ ≤ Fintype.card ((Fin m → ZMod 2) × (Fin m → ZMod 2)) :=
      Fintype.card_le_of_surjective outer covers
    _ = 2 ^ m * 2 ^ m := by rw [Fintype.card_prod, vector_card]
    _ = 2 ^ (2 * m) := by rw [← pow_add, two_mul]

theorem binary_matrix_card (m : Nat) :
    Fintype.card (Matrix (Fin m) (Fin m) (ZMod 2)) = 2 ^ (m * m) := by
  change Fintype.card (Fin m → Fin m → ZMod 2) = _
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, pow_mul]

theorem uniform_rank_le_one_probability_le (m : Nat) :
    (FiniteDistribution.uniform (Matrix (Fin m) (Fin m) (ZMod 2))).probability
        (fun A => decide (A.rank ≤ 1)) ≤
      (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) := by
  have hcount :
      (Fintype.card {A : Matrix (Fin m) (Fin m) (ZMod 2) // A.rank ≤ 1} : ℝ) ≤
        (2 : ℝ) ^ (2 * m) := by
    exact_mod_cast binary_rank_le_one_card_le m
  calc
    _ = (∑ A : Matrix (Fin m) (Fin m) (ZMod 2),
          if A.rank ≤ 1 then (1 : ℝ) else 0) /
        (Fintype.card (Matrix (Fin m) (Fin m) (ZMod 2)) : ℝ) := by
      change (∑ A : Matrix (Fin m) (Fin m) (ZMod 2),
        if decide (A.rank ≤ 1) then
          1 / (Fintype.card (Matrix (Fin m) (Fin m) (ZMod 2)) : ℝ) else 0) = _
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro A _
      by_cases hA : A.rank ≤ 1 <;> simp [hA]
    _ = (Fintype.card {A : Matrix (Fin m) (Fin m) (ZMod 2) // A.rank ≤ 1} : ℝ) /
        (Fintype.card (Matrix (Fin m) (Fin m) (ZMod 2)) : ℝ) := by
      simp only [Fintype.card_subtype, Finset.sum_boole]
    _ ≤ (2 : ℝ) ^ (2 * m) /
        (Fintype.card (Matrix (Fin m) (Fin m) (ZMod 2)) : ℝ) :=
      div_le_div_of_nonneg_right hcount (Nat.cast_nonneg _)
    _ = (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) := by
      rw [binary_matrix_card]
      norm_cast

end
end PerfectCompleteness.BinaryRankOneCount

end

end OAI
