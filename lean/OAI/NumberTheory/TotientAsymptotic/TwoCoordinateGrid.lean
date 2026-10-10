import OAI.NumberTheory.TotientAsymptotic.CappedLoglogGrid
import OAI.NumberTheory.TotientAsymptotic.FordCoordinateBounds

namespace OAI

/-! Extract two admissible integer cutoffs from a violating actual preimage. -/
noncomputable section
namespace TotientAsymptotic

lemma two_coordinate_grid {x ω : ℝ} {n K L : ℕ} (hx : 4 ≤ x)
    (hBx : 12 ≤ B x) (hω : 0 ≤ ω) (hn : 0 < n) (hφ : (n.totient:ℝ) ≤ x)
    (hbad : (1+ω)*B x < a 1*fordPrimeCoordinate n 1+a 2*fordPrimeCoordinate n 2)
    (hK : 2 ≤ K) (hKU : (K:ℝ) ≤ B x+2) (hLK : L ≤ K)
    (hL : (L:ℝ)+2 ≤ B x/2) :
    let i := cappedLoglogIndex K (B (fordPrime n 1))
    let j := cappedLoglogIndex K (B (fordPrime n 2))
    3 ≤ n.primeFactorsList.length ∧ 2 ≤ i ∧ i ≤ K ∧ 2 ≤ j ∧ j ≤ K ∧
      loglogCutoff L ≤ loglogCutoff j ∧ loglogCutoff j ≤ loglogCutoff i ∧
      loglogCutoff i < fordPrime n 1 ∧ loglogCutoff j < fordPrime n 2 ∧
      B (loglogCutoff i) ≤ K ∧ Real.log (loglogCutoff i) ≤ Real.exp K ∧
      (1+ω)*B x-(3/2:ℝ)*(B x+5-K) ≤
        a 1*B (loglogCutoff i)+a 2*B (loglogCutoff j) := by
  obtain ⟨hraw2,hlen⟩ := two_coordinate_failure_large_second hx hBx hω hn hφ hbad
  have hp1 := fordPrime_prime (n:=n) (i:=1) (by omega)
  have hp2 := fordPrime_prime (n:=n) (i:=2) (by omega)
  have horder : fordPrime n 2 ≤ fordPrime n 1 := fordPrime_antitone (by omega) (by omega) (by norm_num)
  have hBord : B (fordPrime n 2) ≤ B (fordPrime n 1) :=
    Real.log_le_log (Real.log_pos (by exact_mod_cast hp2.one_lt))
      (Real.log_le_log (by exact_mod_cast hp2.pos) (by exact_mod_cast horder))
  change 4 < B (fordPrime n 2) at hraw2
  have hraw1 : 0 ≤ B (fordPrime n 1) := by linarith
  have hc1 : fordPrimeCoordinate n 1=B (fordPrime n 1) := max_eq_right hraw1
  have hc2 : fordPrimeCoordinate n 2=B (fordPrime n 2) := max_eq_right (show 0 ≤ B (fordPrime n 2) by linarith)
  have hb1 := (ford_coordinate_upper hx hn hφ 1)
  have hb2 := (ford_coordinate_upper hx hn hφ 2)
  rw [hc1] at hb1
  rw [hc2] at hb2
  have hi := capped_loglog_prime hK hKU hp1.one_lt (by linarith) hb1
  have hj := capped_loglog_prime hK hKU hp2.one_lt hraw2.le hb2
  dsimp only at hi hj ⊢
  have hLraw : (L:ℝ)+1 ≤ B (fordPrime n 2) := by
    have hh := two_coordinate_failure_second_lower hx (by linarith) hω hn hφ hbad
    rw [hc2] at hh
    linarith
  have hLj := cappedLoglogIndex_lower hLK hLraw
  have hji := cappedLoglogIndex_mono K hBord
  refine ⟨hlen,hi.1,hi.2.1,hj.1,hj.2.1,loglogCutoff_mono (by exact_mod_cast hLj),
    loglogCutoff_mono (by exact_mod_cast hji),hi.2.2.1,hj.2.2.1,hi.2.2.2.2.1,hi.2.2.2.2.2,?_⟩
  obtain ⟨ha1,ha1',ha2,ha2'⟩ := first_two_a_bounds
  have hpos : 0 ≤ B x+5-K := by linarith
  have ha : a 1+a 2 ≤ (3/2:ℝ) := by linarith
  have hcost := mul_le_mul_of_nonneg_right ha hpos
  have hm1 := mul_le_mul_of_nonneg_left hi.2.2.2.1 ha1.le
  have hm2 := mul_le_mul_of_nonneg_left hj.2.2.2.1 ha2.le
  rw [hc1,hc2] at hbad
  nlinarith only [hbad,hm1,hm2,hcost]

end TotientAsymptotic

end

end OAI
