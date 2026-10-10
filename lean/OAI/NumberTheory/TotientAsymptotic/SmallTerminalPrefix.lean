import OAI.NumberTheory.TotientAsymptotic.FailedRowPrefix
import OAI.NumberTheory.TotientAsymptotic.StrictCofactorSplit

namespace OAI

/-! A bounded terminal coordinate supplies an exact smooth residual split. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_prime_le_exp_exp {n j : ℕ} {t : ℝ} (_ht : 0 ≤ t)
    (hj : fordPrimeCoordinate n j ≤ t) :
    (fordPrime n j:ℝ) ≤ Real.exp (Real.exp t) := by
  by_cases hp : fordPrime n j=1
  · rw [hp,Nat.cast_one]
    exact Real.one_le_exp (Real.exp_pos _).le
  have hp1 : (1:ℝ) < fordPrime n j := by
    exact_mod_cast (show 1 < fordPrime n j from lt_of_le_of_ne (fordPrime_pos n j) (Ne.symm hp))
  have hlog : 0 < Real.log (fordPrime n j:ℝ) := Real.log_pos hp1
  have hh : Real.log (Real.log (fordPrime n j:ℝ)) ≤ t := (le_max_right _ _).trans hj
  have he : Real.log (fordPrime n j:ℝ) ≤ Real.exp t :=
    (Real.log_le_iff_le_exp hlog).mp hh
  exact (Real.log_le_iff_le_exp (zero_lt_one.trans hp1)).mp he

lemma small_terminal_gap {n j : ℕ} {t : ℝ} (_hj : 0 < j)
    (hprev : t < fordPrimeCoordinate n (j-1))
    (hcur : fordPrimeCoordinate n j ≤ t) :
    fordPrime n j < fordPrime n (j-1) :=
  fordPrime_lt_of_coordinate_lt (hcur.trans_lt hprev)

lemma small_terminal_index {n j : ℕ} {t : ℝ} (hj : 0 < j) (ht : 0 ≤ t)
    (hprev : t < fordPrimeCoordinate n (j-1)) :
    j ≤ n.primeFactorsList.length := by
  have hp : 0 < fordPrimeCoordinate n (j-1) := ht.trans_lt hprev
  have hi := fordPrime_index_of_doubleLog_pos (by
    rw [← fordPrimeCoordinate_eq_raw_of_pos hp]
    exact hp)
  omega

lemma terminal_prefix_conditions {x t : ℝ} {n L j : ℕ}
    (hj : 2 ≤ j) (hjL : j ≤ L) (ht : (1/100:ℝ) ≤ t)
    (hprev : t < fordPrimeCoordinate n (j-1))
    (hrows : ∀ i < j,fordRowSum L (fordPrimeCoordinate n) i ≤
      xi x i*(if i=0 then B x else fordPrimeCoordinate n i)) :
    (∀ i,(fordPrefixPrimes n (j-1) i).Prime) ∧
    primePrefixCoord (fordPrefixPrimes n (j-1)) ∈
      enlargedSimplex (j-1) (B x) (xi x 0) (fun i => xi x (i.val+1)) ∧
    (∀ i,i.val+1=j-1 → (1/100:ℝ) ≤ primePrefixCoord (fordPrefixPrimes n (j-1)) i) := by
  have hp (i : Fin (j-1)) : 0 < fordPrimeCoordinate n (i.val+1) := by
    have ho := ford_coordinate_antitone n (show i.val+1 ≤ j-1 by omega)
    linarith only [ho,hprev,ht]
  have he : primePrefixCoord (fordPrefixPrimes n (j-1))=
      fun i : Fin (j-1) => fordPrimeCoordinate n (i.val+1) := by
    funext i
    exact (fordPrimeCoordinate_eq_raw_of_pos (hp i)).symm
  refine ⟨fun i => fordPrime_prime (fordPrime_index_of_doubleLog_pos
    (by rw [← fordPrimeCoordinate_eq_raw_of_pos (hp i)]; exact hp i)),?_,?_⟩
  · rw [he]
    exact rows_give_enlarged_prefix (by omega) _ (fun _ => le_max_left _ _)
      (fun i hi => hrows i (by omega))
  · intro i hi
    rw [he]
    change (1/100:ℝ) ≤ fordPrimeCoordinate n (i.val+1)
    rw [hi]
    linarith only [ht,hprev]

lemma small_terminal_smooth {n j : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hcur : fordPrimeCoordinate n j ≤ t) :
    (largestPrimeFactor (fordCofactor n j).totient:ℝ) ≤ Real.exp (Real.exp t) := by
  have hh := (largestPrimeFactor_totient_le (fordCofactor n j)).trans_eq (fordCofactor_largest_exact n j)
  exact (Nat.cast_le.mpr hh).trans (ford_prime_le_exp_exp ht hcur)

lemma first_small_terminal_exists {n L : ℕ} {t : ℝ}
    (hhead : t < fordPrimeCoordinate n 0) (htail : fordPrimeCoordinate n L ≤ t) :
    ∃ j,1 ≤ j ∧ j ≤ L ∧ t < fordPrimeCoordinate n (j-1) ∧
      fordPrimeCoordinate n j ≤ t := by
  classical
  let h : ∃ j,fordPrimeCoordinate n j ≤ t := ⟨L,htail⟩
  let j := Nat.find h
  have hj := Nat.find_spec h
  change fordPrimeCoordinate n j ≤ t at hj
  have hj0 : j≠0 := by
    intro he
    have hh : fordPrimeCoordinate n 0 ≤ t := by simpa only [he] using hj
    exact (not_lt_of_ge hh) hhead
  refine ⟨j,by omega,Nat.find_min' h htail,?_,hj⟩
  exact lt_of_not_ge (Nat.find_min h (show j-1 < j by omega))

end TotientAsymptotic

end

end OAI
