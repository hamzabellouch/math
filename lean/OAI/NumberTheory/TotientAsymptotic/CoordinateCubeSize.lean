import OAI.NumberTheory.TotientAsymptotic.CoordinateCube
import OAI.NumberTheory.TotientAsymptotic.UnbandedCubeCost

namespace OAI

/-! The affine unit-box error at one coordinate depends only on its remaining
dimension, with the same renewal bound as the total box cost. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma coordinateCubeShift_sum (N : ℕ) (i : Fin N) :
    coordinateCubeShift N i = ∑ k∈Finset.range (N-i.val),
      g k*((N-i.val-k:ℕ):ℝ)^2 := by
  rw [coordinateCubeShift_coordinate,←Finset.sum_filter]
  apply Finset.sum_bij (fun j _ => j.val-i.val)
  · intro j hj
    have hj := (Finset.mem_filter.mp hj).2
    exact Finset.mem_range.mpr (by have := j.isLt; change i.val ≤ j.val at hj; omega)
  · intro j hj k hk he
    have hj := (Finset.mem_filter.mp hj).2
    have hk := (Finset.mem_filter.mp hk).2
    apply Fin.ext
    change i.val ≤ j.val at hj
    change i.val ≤ k.val at hk
    omega
  · intro k hk
    have hk := Finset.mem_range.mp hk
    let j : Fin N := ⟨i.val+k,by omega⟩
    refine ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
    · change i.val ≤ i.val+k
      omega
    · dsimp only [j]
      omega
  · intro j hj
    have hj := (Finset.mem_filter.mp hj).2
    have he : N-i.val-(j.val-i.val)=N-j.val := by
      have := j.isLt
      change i.val ≤ j.val at hj
      omega
    rw [he]

lemma coordinateCubeShift_le_cost (N : ℕ) (i : Fin N) :
    coordinateCubeShift N i ≤ prefixCubeCost (N-i.val) := by
  let t:=N-i.val
  have ht : 0<t := by dsimp only [t]; exact Nat.sub_pos_of_lt i.isLt
  rw [coordinateCubeShift_sum]
  change (∑ k∈Finset.range t,g k*((t-k:ℕ):ℝ)^2) ≤ prefixCubeCost t
  rw [show Finset.range t=Finset.range ((t-1)+1) by congr 1; omega,
    Finset.sum_range_succ']
  have hs : (∑ k∈Finset.range (t-1),g (k+1)*((t-(k+1):ℕ):ℝ)^2) ≤
      ∑ k∈Finset.range t,g (k+1)*((t-k:ℕ):ℝ)^2 := by
    apply le_trans (Finset.sum_le_sum ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le t 1)) ?_)
    · intro k _
      apply mul_le_mul_of_nonneg_left _ (g_pos _).le
      apply pow_le_pow_left₀ (Nat.cast_nonneg _) _ 2
      exact_mod_cast (show t-(k+1) ≤ t-k by omega)
    · intro k _ _
      exact mul_nonneg (g_pos _).le (sq_nonneg _)
  have he : (∑ k∈Finset.range t,g (k+1)*((t-k:ℕ):ℝ)^2)=
      ∑ k : Fin t,g (k.val+1)*((t-k.val:ℕ):ℝ)^2 :=
    (Fin.sum_univ_eq_sum_range _ _).symm
  rw [he] at hs
  simp only [Nat.sub_zero,show g 0=1 by simp [g],one_mul]
  unfold prefixCubeCost
  linarith only [hs]

theorem coordinateCubeShift_normalized_bound : ∃ C : ℝ,0<C ∧
    ∀ (N : ℕ) (i : Fin N),coordinateCubeShift N i*rho^(N-i.val) ≤ C := by
  obtain ⟨C,hC,hcost⟩ := prefixCubeCost_normalized_bound
  refine ⟨C,hC,fun N i => ?_⟩
  exact (mul_le_mul_of_nonneg_right (coordinateCubeShift_le_cost N i)
    (pow_pos rho_pos _).le).trans (hcost _)

end TotientAsymptotic

end

end OAI
