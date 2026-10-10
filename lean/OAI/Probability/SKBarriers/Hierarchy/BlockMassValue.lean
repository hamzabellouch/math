import Mathlib
import OAI.Probability.SKBarriers.Gaussian.BlockStein

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

 theorem blockMass_eq_sum (D N k : ℕ) (i : Fin (blockDimension D N k)) :
    blockMass D N k i = ∑ b : Fin (k+1),
      if (blockLevel D N k b).val ≤ i.val then ((k+1 : ℕ) : ℝ)⁻¹ else 0 := by
  unfold blockMass massFromAtoms blockAtom
  calc
    _ = ∑ t : Fin (blockDimension D N k+1), ∑ b : Fin (k+1),
      if blockLevel D N k b = t then
        (if t.val ≤ i.val then ((k+1 : ℕ) : ℝ)⁻¹ else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : t.val ≤ i.val <;> simp only [ht,ite_true,ite_false,ite_self,Finset.sum_const_zero]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem blockMass_at_field (D N k : ℕ) (b : Fin (k+1)) (i : Fin N) :
    blockMass D N k (fieldIndex D N k b i) = (b.val : ℝ)/((k+1 : ℕ) : ℝ) := by
  rw [blockMass_eq_sum]
  have hh (c : Fin (k+1)) : (blockLevel D N k c).val ≤ (fieldIndex D N k b i).val ↔ c < b := by
    simp only [blockLevel_val,fieldIndex_val,Fin.lt_def]
    constructor
    · intro h
      by_contra hn
      have hc : b.val ≤ c.val := by omega
      have hc' := Nat.mul_le_mul_right N hc
      nlinarith [i.isLt]
    · intro h
      have hc := Nat.mul_le_mul_right N h
      nlinarith
  simp only [hh]
  rw [← Finset.sum_filter]
  have hs : Finset.univ.filter (fun c : Fin (k+1) => c < b) = Finset.Iio b := by
    ext c
    simp
  rw [hs]
  simp only [Finset.sum_const,Fin.card_Iio,nsmul_eq_mul,div_eq_mul_inv]
end SK.Analytic

end
end

end

end OAI
