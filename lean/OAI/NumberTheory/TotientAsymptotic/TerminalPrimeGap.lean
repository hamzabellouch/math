import OAI.NumberTheory.TotientAsymptotic.SmallTerminalPrefix

namespace OAI

/-! A valid Ford row forbids three consecutive equal positive coordinates. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_first_two_coefficient_sum : (32/25:ℝ) ≤ a 1+a 2 := by
  have he : a 1+a 2=3*Real.log 3-2 := by norm_num [a]; ring
  rw [he]
  linarith [Real.log_three_gt_d9]

lemma ford_row_forbids_flat_triple {x : ℝ} {n L i : ℕ}
    (hi : i+2 ≤ L) (hpos : 0 < fordPrimeCoordinate n i)
    (h1 : fordPrimeCoordinate n (i+1)=fordPrimeCoordinate n i)
    (h2 : fordPrimeCoordinate n (i+2)=fordPrimeCoordinate n i)
    (hrow : fordRowSum L (fordPrimeCoordinate n) i ≤ xi x i*fordPrimeCoordinate n i) : False := by
  have hs : a 1*fordPrimeCoordinate n (i+1)+a 2*fordPrimeCoordinate n (i+2) ≤
      fordRowSum L (fordPrimeCoordinate n) i := by
    calc
      _ = ∑ r ∈ ({i+1,i+2}:Finset ℕ),a (r-i)*fordPrimeCoordinate n r := by
        simp
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro r hr
          rcases Finset.mem_insert.mp hr with rfl | hr
          · exact Finset.mem_Icc.mpr (by omega)
          · have he := Finset.mem_singleton.mp hr
            subst r
            exact Finset.mem_Icc.mpr (by omega)
        · intro r hr _
          have hr := Finset.mem_Icc.mp hr
          exact mul_nonneg (a_pos (by omega)).le (le_max_left _ _)
  have hxi : xi x i ≤ (10001/10000:ℝ) := by
    have he : Real.exp (-((m x-i:ℕ):ℝ)/40) ≤ 1 := Real.exp_le_one_iff.mpr
      (by have := Nat.cast_nonneg (α:=ℝ) (m x-i); linarith)
    unfold xi
    linarith only [he]
  rw [h1,h2] at hs
  have ha := mul_le_mul_of_nonneg_right ford_first_two_coefficient_sum hpos.le
  have hb := mul_le_mul_of_nonneg_right hxi hpos.le
  nlinarith only [hs,hrow,ha,hb,hpos]

/-- At one of the last two boundaries there is a strict prime gap, and the
residual largest coordinate is exactly the final one. -/
lemma terminal_strict_prime_gap {x : ℝ} {n L : ℕ} (hL : 3 ≤ L)
    (hpos : 0 < fordPrimeCoordinate n L)
    (hrow : fordRowSum L (fordPrimeCoordinate n) (L-2) ≤
      xi x (L-2)*fordPrimeCoordinate n (L-2)) :
    ∃ j : ℕ,L-1 ≤ j ∧ j ≤ L ∧
      fordPrime n j < fordPrime n (j-1) ∧
      fordPrimeCoordinate n j=fordPrimeCoordinate n L := by
  have hprev := ford_coordinate_antitone n (show L-1 ≤ L by omega)
  by_cases hgap : fordPrimeCoordinate n L < fordPrimeCoordinate n (L-1)
  · exact ⟨L,by omega,le_rfl,fordPrime_lt_of_coordinate_lt hgap,rfl⟩
  have he : fordPrimeCoordinate n (L-1)=fordPrimeCoordinate n L := le_antisymm (le_of_not_gt hgap) hprev
  have hprev' := ford_coordinate_antitone n (show L-2 ≤ L-1 by omega)
  have hgap' : fordPrimeCoordinate n (L-1) < fordPrimeCoordinate n (L-2) := by
    by_contra hh
    have he' : fordPrimeCoordinate n (L-2)=fordPrimeCoordinate n (L-1) :=
      le_antisymm (le_of_not_gt hh) hprev'
    apply ford_row_forbids_flat_triple (i:=L-2) (by omega) (by linarith only [he,he',hpos])
      ?_ ?_ hrow
    · simpa only [show L-2+1=L-1 by omega] using he'.symm
    · simpa only [show L-2+2=L by omega] using (he'.trans he).symm
  refine ⟨L-1,le_rfl,by omega,?_,he⟩
  have hh := fordPrime_lt_of_coordinate_lt hgap'
  simpa only [Nat.sub_sub] using hh

end TotientAsymptotic

end

end OAI
