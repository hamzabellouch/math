import OAI.NumberTheory.TwoPoint.Circuits.CircuitRestriction

namespace OAI

/-! Orthogonality after fixing coordinates. Averaging over the fixed bits
removes all cross terms with different original Walsh supports. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma restricted_walshCoefficient {n : ℕ} (f : BooleanCube n → ℝ)
    (L T : Finset (Fin n)) (y : BooleanCube n) :
    walshCoefficient (fun x => f (restrictCube L y x)) T =
      ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (fun S => S ∩ L = T),
        walshCoefficient f S * walsh (S \ L) y := by
  have hf : (fun x => f (restrictCube L y x)) = fun x =>
      ∑ S : Finset (Fin n),
        (walshCoefficient f S * walsh (S \ L) y) * walsh (S ∩ L) x := by
    funext x
    rw [← walsh_inversion f (restrictCube L y x)]
    apply sum_congr rfl
    intro S _
    rw [walsh_restrictCube]
    ring
  rw [hf]
  change cubeAverage (fun x => (∑ S : Finset (Fin n),
      (walshCoefficient f S * walsh (S \ L) y) * walsh (S ∩ L) x) * walsh T x) = _
  simp only [sum_mul]
  rw [cubeAverage_sum, sum_filter]
  apply sum_congr rfl
  intro S _
  simp only [mul_assoc, cubeAverage_mul_const, cubeAverage_walsh_mul]
  split_ifs <;> simp

lemma restriction_support_injective {n : ℕ} (L T S U : Finset (Fin n))
    (hS : S ∩ L = T) (hU : U ∩ L = T) (h : S \ L = U \ L) : S = U := by
  calc
    S = S \ L ∪ S ∩ L := (sdiff_union_inter S L).symm
    _ = U \ L ∪ U ∩ L := by rw [h, hS, hU]
    _ = U := sdiff_union_inter U L

theorem restricted_walshCoefficient_mean_sq {n : ℕ} (f : BooleanCube n → ℝ)
    (L T : Finset (Fin n)) :
    cubeAverage (fun y => (walshCoefficient (fun x => f (restrictCube L y x)) T) ^ 2) =
      ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (fun S => S ∩ L = T),
        (walshCoefficient f S) ^ 2 := by
  let I := (univ : Finset (Finset (Fin n))).filter (fun S => S ∩ L = T)
  have heq : (fun y => (walshCoefficient (fun x => f (restrictCube L y x)) T) ^ 2) =
      fun y => ∑ S ∈ I, ∑ U ∈ I,
        (walshCoefficient f S * walshCoefficient f U) *
          (walsh (S \ L) y * walsh (U \ L) y) := by
    funext y
    rw [restricted_walshCoefficient, pow_two, sum_mul]
    apply sum_congr rfl
    intro S _
    rw [mul_sum]
    apply sum_congr rfl
    intro U _
    ring
  rw [heq, cubeAverage_sum]
  apply sum_congr rfl
  intro S hS
  rw [cubeAverage_sum]
  simp_rw [cubeAverage_mul_const, cubeAverage_walsh_mul]
  rw [sum_eq_single S]
  · simp [pow_two]
  · intro U hU hUS
    have hd : S \ L ≠ U \ L := by
      intro hd
      apply hUS
      exact (restriction_support_injective L T S U
        (mem_filter.mp hS).2 (mem_filter.mp hU).2 hd).symm
    simp [hd]
  · exact fun h => (h hS).elim

theorem restricted_fourier_tail_mean {n : ℕ} (f : BooleanCube n → ℝ)
    (L : Finset (Fin n)) (t : ℕ) :
    cubeAverage (fun y => cubeAverage (fun x =>
      (f (restrictCube L y x) - walshTruncation (fun z => f (restrictCube L y z)) t x) ^ 2)) =
      ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (fun S => t < (S ∩ L).card),
        (walshCoefficient f S) ^ 2 := by
  simp_rw [walshTruncation_error]
  rw [cubeAverage_sum]
  simp_rw [restricted_walshCoefficient_mean_sq, sum_filter]
  have hsum (T : Finset (Fin n)) :
      (if t < T.card then ∑ S : Finset (Fin n),
        if S ∩ L = T then (walshCoefficient f S) ^ 2 else 0 else 0) =
      ∑ S : Finset (Fin n), if t < T.card then
        (if S ∩ L = T then (walshCoefficient f S) ^ 2 else 0) else 0 := by
    by_cases h : t < T.card <;> simp [h]
  simp_rw [hsum]
  rw [sum_comm]
  apply sum_congr rfl
  intro S _
  rw [sum_eq_single (S ∩ L)]
  · simp
  · intro T _ hT
    by_cases ht : t < T.card <;> simp [ht, Ne.symm hT]
  · intro h
    exact (h (mem_univ _)).elim

end TwoPointCorrelations

end OAI
