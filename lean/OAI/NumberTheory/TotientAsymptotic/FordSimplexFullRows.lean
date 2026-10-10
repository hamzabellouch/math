import OAI.NumberTheory.TotientAsymptotic.FordSimplexRows

namespace OAI

/-! At the full natural dimension, Ford's special final row implies the full row. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_simplex_full_rows {x : ℝ} {n : ℕ}
    (hs : fordSimplexCondition x 0 n) :
    ∀ i < m x,fordRowSum (m x) (fordPrimeCoordinate n) i ≤
      xi x i*(if i=0 then B x else fordPrimeCoordinate n i) := by
  intro i hi
  have hh := hs.2.2 i (Finset.mem_Ico.mpr ⟨Nat.zero_le _,by simpa using hi⟩)
  simp only [Nat.sub_zero] at hh
  have hlast : fordSimplexCoordinate x n (m x)=fordPrimeCoordinate n (m x) := by
    rw [fordSimplexCoordinate,ite_eq_right (by omega : m x≠0)]
  by_cases he : i+1=m x
  · rw [ite_eq_left he,hlast] at hh
    have hrow : fordRowSum (m x) (fordPrimeCoordinate n) i=
        a 1*fordPrimeCoordinate n (m x) := by
      unfold fordRowSum
      rw [he,Finset.Icc_self,Finset.sum_singleton,show m x-i=1 by omega]
    rw [hrow]
    have hbound : a 1*fordPrimeCoordinate n (m x) ≤ fordPrimeCoordinate n (m x) := by
      have hh := mul_le_mul_of_nonneg_right (a_le_index (j:=1) le_rfl)
        (show 0 ≤ fordPrimeCoordinate n (m x) from le_max_left _ _)
      simpa using hh
    exact hbound.trans hh
  · rw [ite_eq_right he] at hh
    have hsum : (∑ r ∈ Finset.Icc (i+1) (m x),a (r-i)*fordSimplexCoordinate x n r)=
        fordRowSum (m x) (fordPrimeCoordinate n) i := by
      unfold fordRowSum
      apply Finset.sum_congr rfl
      intro r hr
      rw [fordSimplexCoordinate,ite_eq_right (by have := (Finset.mem_Icc.mp hr).1; omega : r≠0)]
    rwa [hsum] at hh

end TotientAsymptotic

end

end OAI
