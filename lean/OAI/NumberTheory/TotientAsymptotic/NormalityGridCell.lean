import OAI.NumberTheory.TotientAsymptotic.NormalityGrid
import OAI.NumberTheory.TotientAsymptotic.NormalityIntervalTail
import OAI.NumberTheory.TotientAsymptotic.NormalInternalDiscard

namespace OAI

/-! Summing the interval deviations over the finite normality grid. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma normalityGridPoint_two_le (j : ℕ) : (2:ℝ) ≤ normalityGridPoint j := by
  have h1 := Real.one_le_exp (Nat.cast_nonneg j : (0:ℝ) ≤ j)
  have h2 := Real.add_one_le_exp (Real.exp (j:ℝ))
  dsimp [normalityGridPoint]
  linarith

def normalityGridCell (A : ℝ) (M : ℕ) (Q : Finset ℕ) (ij : ℕ×ℕ) : Finset ℕ :=
  Q.filter (fun n => 1 ≤ ij.1 ∧ ij.1 < ij.2 ∧ ij.2 ≤ M ∧ A ≤ (ij.2:ℝ)-1 ∧
    Real.sqrt (A*((ij.2:ℝ)-1))-4 ≤
      |(omegaIn n (normalityGridPoint ij.1) (normalityGridPoint ij.2):ℝ)-((ij.2:ℝ)-ij.1)|)

lemma normality_grid_cell_mass : ∃ C : ℝ, 0<C ∧ ∀ N M : ℕ,
    2 ≤ N → normalityGridPoint M ≤ N → ∀ A : ℝ, 0<A → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,0<n ∧ n ≤ N) → ∀ ij : ℕ×ℕ,
    (∑ n ∈ normalityGridCell A M Q ij,(n:ℝ)⁻¹) ≤ C*Real.log N*Real.exp (-A/6) := by
  classical
  obtain ⟨C,hC,hbound⟩ := normality_interval_mass
  refine ⟨C,hC,?_⟩
  intro N M hN hMN A hA Q hQ ij
  by_cases he : (normalityGridCell A M Q ij).Nonempty
  · obtain ⟨m,hm⟩ := he
    obtain ⟨_,hi,hij,hj,hD,_⟩ := Finset.mem_filter.mp hm
    apply hbound N hN (normalityGridPoint ij.1) (normalityGridPoint ij.2) A ((ij.2:ℝ)-1)
      (normalityGridPoint_two_le _) (normalityGridPoint_mono hij).le
      ((normalityGridPoint_mono.monotone hj).trans hMN) hA hD
    · rw [normalityGridPoint_B,normalityGridPoint_B]
      have hiR : (1:ℝ) ≤ ij.1 := by exact_mod_cast hi
      linarith
    · intro n hn
      obtain ⟨hn,_,_,_,_,hh⟩ := Finset.mem_filter.mp hn
      exact ⟨(hQ n hn).1,(hQ n hn).2,by simpa only [normalityGridPoint_B] using hh⟩
  · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]
    exact mul_nonneg (mul_nonneg hC.le (Real.log_nonneg
      (by exact_mod_cast (show 1 ≤ N by omega)))) (Real.exp_pos _).le

end TotientAsymptotic

end

end OAI
