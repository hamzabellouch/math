import OAI.Analysis.Laughlin.FourBody.Parity
import OAI.Analysis.Laughlin.FourBody.SlaterCoefficient

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

noncomputable def limitSliceCoefficient (r D p j k : ℕ) : ℝ :=
  if p+j+k=D then fourBodyLimitCoefficient r D D p j k else 0

theorem limitSliceCoefficient_antisymmetric (r D p j k : ℕ) (hr : r ≤ D) (ho : Odd r) :
    limitSliceCoefficient r D p k j = -limitSliceCoefficient r D p j k := by
  unfold limitSliceCoefficient
  by_cases h : p+j+k=D
  · rw [ite_eq_left (by omega : p+k+j=D),ite_eq_left h,
      fourBodyLimitCoefficient_antisymmetric r D D p j k ho hr (le_refl _) h]
  · rw [ite_eq_right (by omega : p+k+j ≠ D),ite_eq_right h,neg_zero]

theorem sum_pairLimit_slice (D r a b c d : ℕ) (hab : a < b) (hT : a+b+c+d=D+1) :
    (∑ p ∈ Finset.range (D+1), Real.sqrt 2 * pairLimitCoefficient p a b *
      limitSliceCoefficient r D p c d) = limitSlaterTerm D r a b c d := by
  rw [Finset.sum_eq_single (a+b-1)]
  · rw [limitSliceCoefficient,ite_eq_left (by omega)]
    rfl
  · intro p hp hne
    have h : a+b ≠ p+1 := by omega
    simp [pairLimitCoefficient,h]
  · intro h
    have hm : a+b-1 ∈ Finset.range (D+1) := Finset.mem_range.mpr (by omega)
    exact (h hm).elim

end Laughlin.Spin

end OAI
