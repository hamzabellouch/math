import OAI.NumberTheory.TotientAsymptotic.TerminalSliceCount
import OAI.NumberTheory.TotientAsymptotic.TerminalPrimeGap
import OAI.NumberTheory.TotientAsymptotic.FordSimplexFullRows
import OAI.NumberTheory.TotientAsymptotic.UniformPrefactor
import OAI.NumberTheory.TotientAsymptotic.RenewalInput

namespace OAI

/-! Count all full-simplex values by the final two strict prime boundaries. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem ford_simplex_good_value_count : ∃ C : ℝ,0 < C ∧
    ∀ᶠ x : ℝ in atTop,∀ Q : Finset ℕ,∀ n : ℕ → ℕ,
    (∀ v ∈ Q,0 < n v ∧ (n v).totient=v ∧
      x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧ (v:ℝ) ≤ x ∧ fordSimplexCondition x 0 (n v)) →
    (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (m x) := by
  classical
  obtain ⟨A,hA,hcountA⟩ := terminal_slice_value_count 0
  obtain ⟨D,hD,hcountD⟩ := terminal_slice_value_count 1
  obtain ⟨J,hJ,hproj⟩ := uniform_projected_volume_bound fordRenewalInput
  have hr := rho_pos
  refine ⟨A*J+D*J^2*rho,by positivity,?_⟩
  filter_upwards [hcountA,hcountD,hproj,m_tendsto.eventually (eventually_ge_atTop 4),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ)),eventually_gt_atTop (1:ℝ)]
    with x hcountA hcountD hproj hm hB hx1
  intro Q n hQ
  let U := Q.filter (fun v => fordPrime (n v) (m x) < fordPrime (n v) (m x-1))
  let W := Q\U
  have hrows (v) (hv : v ∈ Q) := ford_simplex_full_rows (hQ v hv).2.2.2.2
  have hlast (v) (hv : v ∈ Q) : 2 < fordPrimeCoordinate (n v) (m x) := by
    simpa only [Nat.sub_zero] using (hQ v hv).2.2.2.2.1
  have hlen (v) (hv : v ∈ Q) : m x < (n v).primeFactorsList.length := by
    apply fordPrime_index_of_doubleLog_pos
    rw [← fordPrimeCoordinate_eq_raw_of_pos (by linarith only [hlast v hv])]
    linarith only [hlast v hv]
  have hU0 := hcountA (m x-2) (by omega) U n (by
    intro v hv
    obtain ⟨hv,hgap⟩ := Finset.mem_filter.mp hv
    obtain ⟨hn,hφ,hhead,hvx,_⟩ := hQ v hv
    have hindex : m x-2+2=m x := by omega
    have hprev : m x-2+1=m x-1 := by omega
    refine ⟨hn,hφ,hhead,hvx,?_,?_,?_,?_⟩
    · rw [hindex]; exact (hlen v hv).le
    · simpa only [hindex,hprev] using hgap
    · simpa only [hindex] using hlast v hv
    · simpa only [hindex] using hrows v hv)
  have hW0 := hcountD (m x-3) (by omega) W n (by
    intro v hv
    obtain ⟨hv,hnot⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨hn,hφ,hhead,hvx,_⟩ := hQ v hv
    have hnotgap : ¬fordPrime (n v) (m x) < fordPrime (n v) (m x-1) := by
      intro hh
      exact hnot (Finset.mem_filter.mpr ⟨hv,hh⟩)
    have hrow : fordRowSum (m x) (fordPrimeCoordinate (n v)) (m x-2) ≤
        xi x (m x-2)*fordPrimeCoordinate (n v) (m x-2) := by
      simpa only [ite_eq_right (show m x-2 ≠ 0 by omega)] using
        hrows v hv (m x-2) (by omega)
    have hh := terminal_strict_prime_gap (by omega : 3 ≤ m x)
      (by linarith only [hlast v hv]) hrow
    obtain ⟨j,hjlo,hjhi,hgap,heq⟩ := hh
    have hj : j=m x-1 := by
      have hjne : j≠m x := by intro he; subst j; exact hnotgap hgap
      omega
    rw [hj] at hgap heq
    have hindex : m x-3+2=m x-1 := by omega
    have hprev : m x-3+1=m x-2 := by omega
    refine ⟨hn,hφ,hhead,hvx,?_,?_,?_,?_⟩
    · have hh := hlen v hv
      rw [hindex]
      omega
    · simpa only [hindex,hprev,Nat.sub_sub] using hgap
    · rw [hindex,heq]; exact hlast v hv
    · intro i hi
      exact hrows v hv i (by omega))
  have hU : (U.card:ℝ) ≤ A*(x/Real.log x)*G x (m x-1) := by
    simpa only [show m x-2+1=m x-1 by omega] using hU0
  have hW : (W.card:ℝ) ≤ D*(x/Real.log x)*G x (m x-2) := by
    simpa only [show m x-3+1=m x-2 by omega] using hW0
  have hg1 := (div_le_iff₀ (G_pos hB (m x))).mp (hproj 1 (by omega))
  have hg2 := (div_le_iff₀ (G_pos hB (m x))).mp (hproj 2 (by omega))
  norm_num only [pow_one,Nat.sub_self,zero_div,pow_zero,mul_one] at hg1
  norm_num only [Nat.reduceSub,Nat.reduceMul,Nat.reduceDiv,pow_one] at hg2
  have hnormal : 0 ≤ x/Real.log x := div_nonneg (by linarith only [hx1]) (Real.log_pos hx1).le
  have hUb := hU.trans (mul_le_mul_of_nonneg_left hg1 (mul_nonneg hA.le hnormal))
  have hWb := hW.trans (mul_le_mul_of_nonneg_left hg2 (mul_nonneg hD.le hnormal))
  have hcard : (Q.card:ℝ)=(U.card:ℝ)+(W.card:ℝ) := by
    have hh := Finset.card_sdiff_add_card_eq_card (show U ⊆ Q from Finset.filter_subset _ _)
    exact_mod_cast (show Q.card=U.card+W.card by dsimp [W]; omega)
  rw [hcard]
  calc
    _ ≤ A*(x/Real.log x)*(J*G x (m x))+D*(x/Real.log x)*(J^2*rho*G x (m x)) := add_le_add hUb hWb
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
