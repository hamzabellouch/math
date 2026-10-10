import Mathlib
import OAI.Combinatorics.KMedian.Compression.GaussianTabulated
import OAI.Combinatorics.KMedian.Compression.GaussianResidualHeight

namespace OAI


                                              
section
namespace MetricKMedian.Gaussian
open Finset

structure MatrixState where
  rows : ℕ
  cols : ℕ
  data : RatMatrix rows cols

def kernelStates : (r n : ℕ) → RatMatrix r n → List MatrixState
  | 0, n, A => [⟨0,n,A⟩]
  | r+1, 0, A => [⟨r+1,0,A⟩]
  | r+1, n+1, A =>
    ⟨r+1,n+1,A⟩ ::
    if h : (univ.filter (fun j => values A 0 j ≠ 0)).Nonempty then
      kernelStates r n (tabulate (residual (values A) ((univ.filter (fun j => values A 0 j ≠ 0)).min' h)))
    else kernelStates r (n+1) (tabulate (fun i j => values A i.succ j))

 theorem kernelStates_length (r n : ℕ) (A : RatMatrix r n) :
    (kernelStates r n A).length ≤ r+1 := by
  induction r generalizing n with
  | zero => simp only [kernelStates,List.length_singleton,le_refl]
  | succ r ih =>
      cases n with
      | zero => simp only [kernelStates,List.length_singleton]; omega
      | succ n =>
          rw [kernelStates,List.length_cons]
          split_ifs with h
          · have hb := ih n (tabulate (residual (values A) ((univ.filter (fun j => values A 0 j ≠ 0)).min' h)))
            omega
          · have hb := ih (n+1) (tabulate (fun i j => values A i.succ j))
            omega

 theorem kernelStates_certificate {R N : ℕ} (original : Fin R → Fin N → ℚ)
    (r n : ℕ) (A : RatMatrix r n) (P : ResidualCertificate original (values A)) :
    ∀ B ∈ kernelStates r n A, Nonempty (ResidualCertificate original (values B.data)) := by
  induction r generalizing n with
  | zero =>
      intro B hB
      simp only [kernelStates,List.mem_singleton] at hB
      subst B
      exact ⟨P⟩
  | succ r ih =>
      cases n with
      | zero =>
          intro B hB
          simp only [kernelStates,List.mem_singleton] at hB
          subst B
          exact ⟨P⟩
      | succ n =>
          intro B hB
          rw [kernelStates,List.mem_cons] at hB
          rcases hB with rfl | hB
          · exact ⟨P⟩
          · split_ifs at hB with h
            · let p := (univ.filter (fun j => values A 0 j ≠ 0)).min' h
              have hp : values A 0 p ≠ 0 := (mem_filter.mp (min'_mem _ h)).2
              have PP : ResidualCertificate original (values (tabulate (residual (values A) p))) := by
                rw [values_tabulate]
                exact P.pivot p hp
              exact ih n _ PP B hB
            · have PP : ResidualCertificate original (values (tabulate (fun i j => values A i.succ j))) := by
                rw [values_tabulate]
                exact P.skip
              exact ih (n+1) _ PP B hB

 theorem kernelStates_underdetermined (r n : ℕ) (A : RatMatrix r n) (hn : r<n) :
    ∀ B ∈ kernelStates r n A, B.rows<B.cols := by
  induction r generalizing n with
  | zero =>
      intro B hB
      simp only [kernelStates,List.mem_singleton] at hB
      subst B
      exact hn
  | succ r ih =>
      cases n with
      | zero => omega
      | succ n =>
          intro B hB
          rw [kernelStates,List.mem_cons] at hB
          rcases hB with rfl | hB
          · exact hn
          · split_ifs at hB with h
            · exact ih n _ (by omega) _ hB
            · exact ih (n+1) _ (by omega) _ hB

 theorem kernelStates_entry_height (R N L : ℕ) (A : RatMatrix R N)
    (hnum : ∀ i j, |(values A i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((values A i j).den:ℤ) ≤ (2:ℤ)^L)
    (B : MatrixState) (hB : B ∈ kernelStates R N A) (i : Fin B.rows) (j : Fin B.cols) :
    |(values B.data i j).num| ≤ (2:ℤ)^(residualHeight R N L) ∧
      ((values B.data i j).den:ℤ) ≤ (2:ℤ)^(residualHeight R N L) := by
  obtain ⟨P⟩ := kernelStates_certificate (values A) R N A (ResidualCertificate.initial _) B hB
  exact P.entry_height L hnum hden i j

def returnHeight (R N L : ℕ) : ℕ := 2*R*(R+residualHeight R N L*(N+1))

 theorem kernelStates_return_height (R N L : ℕ) (A : RatMatrix R N) (hRN : R<N)
    (hnum : ∀ i j, |(values A i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((values A i j).den:ℤ) ≤ (2:ℤ)^L)
    (B : MatrixState) (hB : B ∈ kernelStates R N A) (j : Fin B.cols) :
    |((kernelVector B.rows B.cols B.data)[j.val]).num| ≤ (2:ℤ)^(returnHeight R N L) ∧
      (((kernelVector B.rows B.cols B.data)[j.val]).den:ℤ) ≤ (2:ℤ)^(returnHeight R N L) := by
  obtain ⟨P⟩ := kernelStates_certificate (values A) R N A (ResidualCertificate.initial _) B hB
  have hrow : B.rows ≤ R := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective P.row P.row_injective
  have hcol : B.cols ≤ N := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective P.col P.col_injective
  have hentry := kernelStates_entry_height R N L A hnum hden B hB
  have hb := rational_input_kernel_bounds B.rows B.cols (residualHeight R N L) (values B.data)
    (kernelStates_underdetermined R N A hRN B hB) (fun i j => (hentry i j).1) (fun i j => (hentry i j).2) j
  have hp : 2*B.rows*(B.rows+residualHeight R N L*(B.cols+1)) ≤ returnHeight R N L := by
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hrow)
      (Nat.add_le_add hrow (Nat.mul_le_mul_left _ (Nat.add_le_add_right hcol 1)))
  have he := congrFun (kernelVector_eq B.rows B.cols B.data) j
  rw [he]
  exact ⟨hb.1.trans (pow_le_pow_right₀ (by norm_num) hp),hb.2.trans (pow_le_pow_right₀ (by norm_num) hp)⟩

end MetricKMedian.Gaussian
end

end OAI
