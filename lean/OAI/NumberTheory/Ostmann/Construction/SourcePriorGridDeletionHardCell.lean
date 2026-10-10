import OAI.NumberTheory.Ostmann.Construction.SourcePriorGridDeletionBasic

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Construction.SourcePriorGridDeletion

def hardPrimes (G : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊Real.exp (G-1)⌋₊ ⌊Real.exp (G+1)⌋₊).filter Nat.Prime

theorem gridMean_eq_hardPrimeSum (G : ℝ) (E : Finset ℕ) (F : ℕ→ℂ) :
    gridMean G E F=∑p∈hardPrimes G,((logCellWeight G p/logCellMass G E:ℝ):ℂ)*F p := by
  have hsub : hardPrimes G⊆logCellPrimes G := by
    intro p hp
    obtain ⟨hpI,hprime⟩ := Finset.mem_filter.mp hp
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ioc.mp hpI
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨by omega,?_⟩,hprime⟩
    exact hhi.trans (Nat.floor_le_ceil _)
  symm
  apply Finset.sum_subset hsub
  intro p hp hnot
  have hprime : p.Prime := (Finset.mem_filter.mp hp).2
  have hnotI : ¬(⌊Real.exp (G-1)⌋₊<p ∧ p≤⌊Real.exp (G+1)⌋₊) := by
    intro h
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr h,hprime⟩)
  have hz : logCellWeight G p=0 := by
    by_cases hlo : ⌊Real.exp (G-1)⌋₊<p
    · apply logCellWeight_zero_above
      have hn : ¬p≤⌊Real.exp (G+1)⌋₊ := fun hh => hnotI ⟨hlo,hh⟩
      omega
    · apply logCellWeight_zero_below
      omega
  simp only [hz,zero_div,Complex.ofReal_zero,zero_mul]

theorem gridMean_eq_hardPrime_prior_sum (G : ℝ) (E : Finset ℕ) (F : ℕ→ℂ) :
    gridMean G E F=∑p∈hardPrimes G,(((logCellMass G E*(p:ℝ))⁻¹:ℝ):ℂ)*
      ((Ostmann.smoothPartition (Real.log p-G):ℂ)*F p) := by
  rw [gridMean_eq_hardPrimeSum]
  apply Finset.sum_congr rfl
  intro p hp
  have he : logCellWeight G p/logCellMass G E=
      (logCellMass G E*(p:ℝ))⁻¹*Ostmann.smoothPartition (Real.log p-G) := by
    simp only [logCellWeight,div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he,Complex.ofReal_mul,mul_assoc]

end Ostmann.Construction.SourcePriorGridDeletion

end

end OAI
