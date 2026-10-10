import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSquarefreePart
import OAI.NumberTheory.Ostmann.QuadraticSieve.PublishedQuadraticSieve

namespace OAI

/-! # Exact finite reindexing of the small-squarefree-kernel contribution -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadraticSquarePart_le {m : ℕ} (hm : 0 < m) : quadraticSquarePart m ≤ m := by
  have ha := quadraticSquarePart_pos hm
  have hb := quadraticSquarefreePart_pos m
  have he := quadraticSquarePart_factor m
  nlinarith [Nat.mul_le_mul_left (quadraticSquarePart m ^ 2) hb]

 theorem quadraticSquarefreePart_dvd (m : ℕ) : quadraticSquarefreePart m ∣ m :=
  ⟨quadraticSquarePart m ^ 2, by rw [mul_comm, quadraticSquarePart_factor]⟩

 theorem quadraticSquarePart_dvd (m : ℕ) : quadraticSquarePart m ∣ m :=
  ⟨quadraticSquarePart m * quadraticSquarefreePart m,
    by rw [← mul_assoc, ← pow_two, quadraticSquarePart_factor]⟩

noncomputable def quadraticSmallKernelRange (M K : ℕ) : Finset ℕ :=
  (Finset.Icc 1 M).filter fun m => Odd m ∧ quadraticSquarefreePart m ≤ K

def quadraticSmallKernelPairs (M K : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 M).product (oddSquarefreeRange K)).filter
    fun z => Odd z.1 ∧ z.1 ^ 2 * z.2 ≤ M

 theorem sum_quadraticSmallKernelRange {R : Type*} [AddCommMonoid R]
    (M K : ℕ) (f : ℕ → R) :
    (∑ m ∈ quadraticSmallKernelRange M K, f m) =
      ∑ z ∈ quadraticSmallKernelPairs M K, f (z.1 ^ 2 * z.2) := by
  symm
  apply Finset.sum_bij (fun z _ => z.1 ^ 2 * z.2)
  · intro z hz
    obtain ⟨hz, ho, hb⟩ := Finset.mem_filter.mp hz
    obtain ⟨ha, hk⟩ := Finset.mem_product.mp hz
    obtain ⟨hkr, hko, hks⟩ := Finset.mem_filter.mp hk
    have ha0 : z.1 ≠ 0 := by have := (Finset.mem_Icc.mp ha).1; omega
    have hf := (quadraticSquarefreePart_of_mul_square ha0 hks).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, hb⟩, ?_, ?_⟩
    · exact Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero ha0) _) (Finset.mem_Icc.mp hkr).1
    · exact ho.pow.mul hko
    · rw [hf]
      exact (Finset.mem_Icc.mp hkr).2
  · intro z hz w hw he
    obtain ⟨hz, _, _⟩ := Finset.mem_filter.mp hz
    obtain ⟨hw, _, _⟩ := Finset.mem_filter.mp hw
    obtain ⟨hza, hzb⟩ := Finset.mem_product.mp hz
    obtain ⟨hwa, hwb⟩ := Finset.mem_product.mp hw
    have ha : z.1 ≠ 0 := by have := (Finset.mem_Icc.mp hza).1; omega
    have hc : w.1 ≠ 0 := by have := (Finset.mem_Icc.mp hwa).1; omega
    have hh := quadratic_squarefree_factor_unique ha hc
      (Finset.mem_filter.mp hzb).2.2 (Finset.mem_filter.mp hwb).2.2 he
    exact Prod.ext hh.1 hh.2
  · intro m hm
    obtain ⟨hr, ho, hk⟩ := Finset.mem_filter.mp hm
    have hm0 : 0 < m := (Finset.mem_Icc.mp hr).1
    refine ⟨(quadraticSquarePart m, quadraticSquarefreePart m), ?_, quadraticSquarePart_factor m⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨quadraticSquarePart_pos hm0,
        (quadraticSquarePart_le hm0).trans (Finset.mem_Icc.mp hr).2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨quadraticSquarefreePart_pos m, hk⟩,
        ho.of_dvd_nat (quadraticSquarefreePart_dvd m), quadraticSquarefreePart_squarefree m⟩
    · exact ho.of_dvd_nat (quadraticSquarePart_dvd m)
    · rw [quadraticSquarePart_factor]
      exact (Finset.mem_Icc.mp hr).2
  · intro _ _
    rfl

end Ostmann

end OAI
