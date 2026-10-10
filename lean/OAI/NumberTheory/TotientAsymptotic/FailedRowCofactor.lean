import OAI.NumberTheory.TotientAsymptotic.FirstFailedRow
import OAI.NumberTheory.TotientAsymptotic.FordCofactorCoordinates

namespace OAI

/-! The failed original row is the first row of its actual residual preimage. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma fordRowSum_cofactor {n L j : ℕ} (hjL : j ≤ L) :
    fordRowSum L (fordPrimeCoordinate n) j =
      ∑ i : Fin (L-j), a (i.val+1)*fordPrimeCoordinate (fordCofactor n j) (i.val+1) := by
  symm
  unfold fordRowSum
  apply Finset.sum_bij (fun i _ => j+i.val+1)
  · intro i _
    exact Finset.mem_Icc.mpr (by have := i.isLt; omega)
  · intro i _ k _ hik
    apply Fin.ext
    omega
  · intro r hr
    have hr := Finset.mem_Icc.mp hr
    refine ⟨⟨r-j-1,by omega⟩,Finset.mem_univ _,?_⟩
    simp only
    omega
  · intro i _
    rw [fordCofactor_coordinate]
    have he : j+i.val+1-j=i.val+1 := by omega
    rw [he]
    congr 2

lemma failed_row_cofactor {x ω : ℝ} {n L j : ℕ} (hjL : j ≤ L)
    (hxi : xi x j=1+ω)
    (hfail : xi x j*fordPrimeCoordinate n j < fordRowSum L (fordPrimeCoordinate n) j) :
    (1+ω)*fordPrimeCoordinate (fordCofactor n j) 0 <
      ∑ i : Fin (L-j), a (i.val+1)*fordPrimeCoordinate (fordCofactor n j) (i.val+1) := by
  rw [fordCofactor_coordinate,Nat.add_zero]
  rwa [hxi,fordRowSum_cofactor hjL] at hfail

end TotientAsymptotic

end

end OAI
