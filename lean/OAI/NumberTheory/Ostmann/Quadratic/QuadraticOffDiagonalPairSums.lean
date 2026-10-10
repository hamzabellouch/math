import OAI.NumberTheory.Ostmann.Quadratic.QuadraticRoughDiagonal
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallMomentMain

namespace OAI

/-! # The original off-diagonal pairs in the two Poisson transforms -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

noncomputable def quadraticSmallPairSum (M K D q : ℕ) : ℂ :=
  ∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
    (jacobiSym b q : ℂ) * ∑' c : ℕ+,
      (1 : DirichletCharacter ℂ (2 * (q * D))) (c : ZMod (2 * (q * D))) *
        quadraticSieveWeight ((c : ℝ) ^ 2 * b / M)

noncomputable def quadraticSmallPairCore (M K D q : ℕ) (J : ℝ) : ℂ :=
  ∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
    (jacobiSym b q : ℂ) * quadraticSmallDyadicCore quadraticSieveWeight M b J (2 * (q * D)) b

theorem quadratic_small_pair_sum_eq {M N D : ℕ} (hM : 0 < M) (K : ℕ)
    {z : ℕ × ℕ} (hz : z ∈ quadraticGcdPairs N D) :
    (∑ m ∈ quadraticSmallKernelRange (3 * M) K,
      quadraticSieveWeight ((m : ℝ) / M) * (jacobiSym m z.1 : ℂ) * (jacobiSym m z.2 : ℂ)) =
        quadraticSmallPairSum M K D (quadraticPairKernel z.1 z.2) := by
  obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz
  rw [quadratic_small_pair_transform hM K (Finset.mem_filter.mp hs).2.2
    (Finset.mem_filter.mp ht).2.2]
  unfold quadraticSmallPairSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  rw [hg]
  have he : (∑' c : ℕ+, (1 : DirichletCharacter ℂ (2 * (z.1 * z.2)))
      (c : ZMod (2 * (z.1 * z.2))) * quadraticSieveWeight ((c : ℝ) ^ 2 * b / M)) =
      ∑' c : ℕ+, (1 : DirichletCharacter ℂ (2 * (quadraticPairKernel z.1 z.2 * D)))
      (c : ZMod (2 * (quadraticPairKernel z.1 z.2 * D))) *
        quadraticSieveWeight ((c : ℝ) ^ 2 * b / M) := by
    apply tsum_congr
    intro c
    rw [quadratic_principal_pair_reduction hg]
  rw [he]
  by_cases hb : D.Coprime b
  · rw [ite_eq_left hb.symm, ite_eq_left hb, one_mul]
  · rw [ite_eq_right (fun h => hb h.symm), ite_eq_right hb, zero_mul, zero_mul]

theorem quadratic_odd_pair_poisson {M N D : ℕ} (hM : 0 < M)
    {z : ℕ × ℕ} (hz : z ∈ quadraticGcdPairs N D) :
    (∑ m ∈ quadraticOddRange (3 * M),
      quadraticSieveWeight ((m : ℝ) / M) * (jacobiSym m z.1 : ℂ) * (jacobiSym m z.2 : ℂ)) =
        quadraticFirstKernelTransform M D (quadraticPairKernel z.1 z.2) := by
  obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz
  have hsf := quadraticPairKernel_squarefree (Finset.mem_filter.mp hs).2.2
    (Finset.mem_filter.mp ht).2.2
  have ho := quadraticPairKernel_odd (Finset.mem_filter.mp hs).2.1 (Finset.mem_filter.mp ht).2.1
  have hD : 0 < D := by
    rw [← hg]
    exact Nat.gcd_pos_of_pos_left _ (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
  have : NeZero D := ⟨hD.ne'⟩
  have : NeZero (quadraticPairKernel z.1 z.2) := ⟨hsf.ne_zero⟩
  unfold quadraticFirstKernelTransform
  rw [← quadratic_odd_kernel_poisson (D := D) hM hsf ho]
  apply Finset.sum_congr rfl
  intro m _
  have hj := congrArg (fun x : ℤ => (x : ℂ))
    (jacobi_pair_kernel (Finset.mem_filter.mp hs).2.2 (Finset.mem_filter.mp ht).2.2 (m : ℤ))
  rw [hg] at hj
  push_cast at hj
  rw [mul_assoc, hj]
  split_ifs <;> ring

theorem quadratic_rough_pair_transform {M N D : ℕ} (hM : 0 < M) (K : ℕ)
    {z : ℕ × ℕ} (hz : z ∈ quadraticGcdPairs N D) :
    (∑ m ∈ quadraticRoughKernelRange (3 * M) K,
      quadraticSieveWeight ((m : ℝ) / M) * (jacobiSym m z.1 : ℂ) * (jacobiSym m z.2 : ℂ)) =
      quadraticFirstKernelTransform M D (quadraticPairKernel z.1 z.2) -
        quadraticSmallPairSum M K D (quadraticPairKernel z.1 z.2) := by
  have hs : (quadraticOddRange (3 * M)).filter
      (fun m => ¬ K < quadraticSquarefreePart m) = quadraticSmallKernelRange (3 * M) K := by
    ext m
    simp only [quadraticOddRange, quadraticSmallKernelRange, Finset.mem_filter, not_lt]
    tauto
  have he := Finset.sum_filter_add_sum_filter_not (quadraticOddRange (3 * M))
    (fun m => K < quadraticSquarefreePart m)
    (fun m => quadraticSieveWeight ((m : ℝ) / M) *
      (jacobiSym m z.1 : ℂ) * (jacobiSym m z.2 : ℂ))
  rw [hs, quadratic_small_pair_sum_eq hM K hz, quadratic_odd_pair_poisson hM hz] at he
  exact eq_sub_of_add_eq he

theorem quadratic_gcd_off_diagonal (N : ℕ) (v : ℕ → ℂ) (E : ℕ → ℕ × ℕ → ℂ) :
    quadraticGcdRemainder N v (fun D z => if z.1 = z.2 then 0 else E D z) =
      ∑ z ∈ ((oddSquarefreeRange N).product (oddSquarefreeRange N)).filter (fun z => z.1 ≠ z.2),
        v z.1 * conj (v z.2) * E (z.1.gcd z.2) z := by
  unfold quadraticGcdRemainder
  have he : (∑ D ∈ Finset.Icc 1 N, ∑ z ∈ quadraticGcdPairs N D,
      v z.1 * conj (v z.2) * (if z.1 = z.2 then 0 else E D z)) =
      ∑ D ∈ Finset.Icc 1 N, ∑ z ∈ quadraticGcdPairs N D,
      v z.1 * conj (v z.2) * (if z.1 = z.2 then 0 else E (z.1.gcd z.2) z) := by
    apply Finset.sum_congr rfl
    intro D _
    apply Finset.sum_congr rfl
    intro z hz
    rw [(Finset.mem_filter.mp hz).2]
  rw [he, ← quadratic_pair_sum_gcd, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : z.1 = z.2 <;> simp [hz]

theorem quadratic_rough_off_diagonal_transform {M : ℕ} (hM : 0 < M)
    (N K : ℕ) (v : ℕ → ℂ) :
    quadraticRoughOffDiagonal M N K v = quadraticGcdRemainder N v (fun D z =>
      if z.1 = z.2 then 0 else
        quadraticFirstKernelTransform M D (quadraticPairKernel z.1 z.2) -
          quadraticSmallPairSum M K D (quadraticPairKernel z.1 z.2)) := by
  rw [quadratic_gcd_off_diagonal]
  unfold quadraticRoughOffDiagonal
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  apply quadratic_rough_pair_transform hM K
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1, rfl⟩

end Ostmann

end OAI
