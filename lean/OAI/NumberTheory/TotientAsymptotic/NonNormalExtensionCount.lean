import OAI.NumberTheory.TotientAsymptotic.PrimeExtensionCoverage
import OAI.NumberTheory.TotientAsymptotic.NormalityInput

namespace OAI

/-! Residual-value grouping for the large-prime half of Ford Lemma 2.8. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

/-- On a nonempty prime interval, its lower cutoff supplies the logarithm
in Ford's exceptional-prime estimate. -/
theorem non_normal_quarter_prime_count : ∃ C : ℝ,0 < C ∧
    ∀ S x : ℝ,2 < S → 4 ≤ x → ∀ d : ℕ,0 < d → ∀ Q : Finset ℕ,
    (∀ p ∈ Q,p.Prime ∧ 4 ≤ p ∧ x^(1/4:ℝ) ≤ p ∧
      ((p-1)*d:ℕ) ≤ x ∧ ¬IsNormalPrime S p) →
    (Q.card:ℝ) ≤ C*x/(d*Real.log x)*(B (2*x))^5*(Real.log S)^(-1/6:ℝ) := by
  classical
  obtain ⟨C,hC,hford⟩ := fordLemma26Input
  refine ⟨8*C,by positivity,?_⟩
  intro S x hS hx d hd Q hQ
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hlS : 0 < Real.log S := Real.log_pos (by linarith)
  have hs : 0 ≤ (Real.log S)^(-1/6:ℝ) := Real.rpow_nonneg hlS.le _
  by_cases hne : Q.Nonempty
  · let N := ⌊1+x/d⌋₊
    have hpN (p : ℕ) (hp : p ∈ Q) : p ≤ N := by
      have hh := (hQ p hp).2.2.2.1
      have hp1 : 1 ≤ p := (hQ p hp).1.one_le
      have hhR : ((p:ℝ)-1)*d ≤ x := by exact_mod_cast hh
      apply Nat.le_floor
      have hdiv := (le_div_iff₀ hd0).mpr hhR
      linarith
    obtain ⟨p,hp⟩ := hne
    have hN4 : 4 ≤ N := (hQ p hp).2.1.trans (hpN p hp)
    have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hN1 : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hlogN : Real.log x/4 ≤ Real.log N := by
      have hlo := (hQ p hp).2.2.1.trans (Nat.cast_le.mpr (hpN p hp))
      have hh := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hlo
      rw [Real.log_rpow hx0] at hh
      linarith
    have hlogN0 : 0 < Real.log N := Real.log_pos hN1
    have hdx : (d:ℝ) ≤ x := by
      have hp1 : 1 ≤ p-1 := by have := (hQ p hp).1.two_le; omega
      exact (Nat.cast_le.mpr (show d ≤ (p-1)*d by nlinarith)).trans (hQ p hp).2.2.2.1
    have hNupper : (N:ℝ) ≤ 2*x/d := by
      have hn : (N:ℝ) ≤ 1+x/d := Nat.floor_le (by positivity)
      have hh : (1:ℝ) ≤ x/d := (le_div_iff₀ hd0).mpr (by simpa using hdx)
      rw [show 2*x/(d:ℝ)=2*(x/d) by ring]
      linarith only [hn,hh]
    have hN2x : (N:ℝ) ≤ 2*x := hNupper.trans ((div_le_iff₀ hd0).mpr (by nlinarith only [hd1,hx0]))
    have hBN : 0 ≤ B N := (doubleLog_nat_pos hN4).le
    have hBmono : B N ≤ B (2*x) := by
      apply Real.log_le_log hlogN0
      exact Real.log_le_log hN0 hN2x
    have hB2 : 0 ≤ B (2*x) := hBN.trans hBmono
    have hsub : Q ⊆ nonNormalPrimes S N := by
      intro q hq
      exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpN q hq,(hQ q hq).1⟩,(hQ q hq).2.2.2.2⟩
    have hcard : (Q.card:ℝ) ≤ (nonNormalPrimes S N).card := Nat.cast_le.mpr (Finset.card_le_card hsub)
    have hrat : C*N/Real.log N ≤ 8*C*x/(d*Real.log x) := by
      calc
        _ ≤ C*(2*x/d)/(Real.log x/4) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hNupper hC.le)
            (by positivity) hlogN
        _ = _ := by ring
    calc
      _ ≤ C*N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ) :=
        hcard.trans (hford S hS N hN4)
      _ ≤ (8*C*x/(d*Real.log x))*(B (2*x))^5*(Real.log S)^(-1/6:ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hs
        exact mul_le_mul hrat (pow_le_pow_left₀ hBN hBmono 5) (by positivity) (by positivity)
      _ = _ := by ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero]
    have hB2 : 0 ≤ B (2*x) := by
      have hh : B 4 ≤ B (2*x) := Real.log_le_log
        (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) (by linarith))
      exact (doubleLog_nat_pos (n:=4) (by norm_num)).le.trans hh
    positivity

end TotientAsymptotic

end

end OAI
