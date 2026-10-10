import Mathlib
import OAI.Combinatorics.KMedian.Optimization.SimplexProjection

namespace OAI

section
section
namespace MetricKMedian.Simplex
open Finset
variable {n : ℕ} [NeZero n]

theorem project_integer_denominator (x : Fin n → ℚ) (X : Fin n → ℤ) (D k : ℤ)
    (hD : 0 < D) (hx : ∀ i, x i=(X i:ℚ)/(D:ℚ)) :
    ∃ (D' : ℤ) (Y : Fin n → ℤ), 0 < D' ∧ D' ≤ D*(n:ℤ) ∧
      ∀ i, project x (k:ℚ) i=(Y i:ℚ)/(D':ℚ) := by
  obtain ⟨a,ha⟩ := level_attained x (k:ℚ)
  let M : ℤ := (upper x a).card
  let c : ℤ := (∑ i ∈ upper x a, X i)-k*D
  have hM : 0 < M := by
    dsimp [M]
    exact_mod_cast upper_card_pos x a
  have hDq : (0:ℚ) < D := by exact_mod_cast hD
  have hMq : (0:ℚ) < M := by exact_mod_cast hM
  have hlevel : level x (k:ℚ)=(c:ℚ)/((D*M:ℤ):ℚ) := by
    rw [ha,threshold]
    simp_rw [hx]
    rw [← sum_div]
    change ((∑ i ∈ upper x a, (X i:ℚ))/(D:ℚ)-(k:ℚ))/(M:ℚ)=_
    simp only [c,Int.cast_sub,Int.cast_sum,Int.cast_mul]
    field_simp
  refine ⟨D*M,fun i => max 0 (X i*M-c),mul_pos hD hM,?_,?_⟩
  · have hc : M ≤ (n:ℤ) := by
      dsimp [M]
      exact_mod_cast ((card_le_univ (upper x a)).trans_eq (Fintype.card_fin n))
    exact mul_le_mul_of_nonneg_left hc hD.le
  · intro i
    unfold project
    rw [hx,hlevel,Int.cast_max,Int.cast_zero]
    rw [Int.cast_mul D M,Int.cast_sub (X i*M) c,Int.cast_mul (X i) M]
    have he : (X i:ℚ)/(D:ℚ)-(c:ℚ)/((D:ℚ)*(M:ℚ))=
        ((X i:ℚ)*(M:ℚ)-(c:ℚ))/((D:ℚ)*(M:ℚ)) := by
      field_simp
    rw [he,← max_div_div_right (mul_pos hDq hMq).le,zero_div]

end MetricKMedian.Simplex
end
end

end OAI
