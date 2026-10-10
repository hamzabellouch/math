import OAI.NumberTheory.TotientAsymptotic.PublishedNormality
import OAI.NumberTheory.TotientAsymptotic.LargestPrimeCount

namespace OAI

/-! The exceptional-prime count on the actual largest-prime interval. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

theorem non_normal_head_count (hford : FordLemma26Input) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ S : ℝ, 2 < S → ∀ D : ℕ, 0 < D →
    ∀ Q : Finset ℕ,
      (∀ p ∈ Q, p.Prime ∧ x^(9/10 : ℝ) ≤ p ∧ ((p-1)*D : ℕ) ≤ x ∧ ¬IsNormalPrime S p) →
      (Q.card : ℝ) ≤ (C*x/((D : ℝ)*Real.log x))*(1+B x)^5*(Real.log S)^(-1/6 : ℝ) := by
  obtain ⟨C,hC,hcount⟩ := hford
  refine ⟨3*C,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ),B_tendsto.eventually (eventually_ge_atTop (0 : ℝ)),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ)<9/10)).eventually (eventually_gt_atTop (4 : ℝ))]
    with x hx2 hB hxpow
  intro S hS D hD Q hQ
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hE : 0 ≤ (Real.log S)^(-1/6 : ℝ) := Real.rpow_nonneg (Real.log_pos (by linarith : 1 < S)).le _
  by_cases hne : Q.Nonempty
  · let Y := 1+x/D
    let N := ⌊Y⌋₊
    have hpY (p : ℕ) (hp : p ∈ Q) : (p : ℝ) ≤ Y := by
      have hh := hQ p hp
      have hpn := hh.1.one_lt.le
      have hv : ((p : ℝ)-1)*D ≤ x := by exact_mod_cast hh.2.2.1
      have hh' := (le_div_iff₀ hD0).mpr hv
      dsimp [Y]
      linarith
    have hsub : Q ⊆ nonNormalPrimes S N := by
      intro p hp
      exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor (hpY p hp),(hQ p hp).1⟩,(hQ p hp).2.2.2⟩
    obtain ⟨p,hp⟩ := hne
    have hpN : (p : ℝ) ≤ N := by exact_mod_cast Nat.le_floor (hpY p hp)
    have hNlo : x^(9/10 : ℝ) ≤ N := (hQ p hp).2.1.trans hpN
    have hN4 : 3 < N := by exact_mod_cast (show (3 : ℝ) < N by linarith)
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hlogN : (9/10 : ℝ)*Real.log x ≤ Real.log (N : ℝ) := by
      have hh := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hNlo
      simpa only [Real.log_rpow hx0] using hh
    have hlogN0 : 0 < Real.log (N : ℝ) := lt_of_lt_of_le (by positivity) hlogN
    have hDx : (D : ℝ) ≤ x := by
      have hp2 := (hQ p hp).1.two_le
      have hh : D ≤ (p-1)*D := by
        simpa only [one_mul] using Nat.mul_le_mul_right D (show 1 ≤ p-1 by omega)
      exact (by exact_mod_cast hh : (D : ℝ) ≤ ((p-1)*D : ℕ)).trans (hQ p hp).2.2.1
    have hY0 : 0 < Y := by dsimp [Y]; positivity
    have hNup : (N : ℝ) ≤ 2*x/D := by
      have hn : (N : ℝ) ≤ Y := Nat.floor_le hY0.le
      have hone : (1 : ℝ) ≤ x/D := (le_div_iff₀ hD0).mpr (by simpa using hDx)
      dsimp [Y] at hn
      calc
        _ ≤ 1+x/D := hn
        _ ≤ 2*(x/D) := by linarith
        _ = _ := by ring
    have hBN0 : 0 ≤ B (N : ℝ) := by
      apply Real.log_nonneg
      have hN4R : (4 : ℝ) ≤ N := by exact_mod_cast (show 4 ≤ N by omega)
      have hlog4 : 1 ≤ Real.log 4 := by rw [Real.log_four_eq]; linarith [Real.log_two_gt_d9]
      exact hlog4.trans (Real.log_le_log (by norm_num) hN4R)
    have hBN : B (N : ℝ) ≤ 1+B x := by
      have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
      have hNX : (N : ℝ) ≤ 2*x := hNup.trans ((div_le_self (by positivity) hD1))
      have hlog2 := Real.log_le_log (by norm_num : (0 : ℝ)<2) hx2
      have h1 : Real.log (N : ℝ) ≤ 2*Real.log x := by
        have hh := Real.log_le_log hN0 hNX
        rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) hx0.ne'] at hh
        linarith
      have hh := Real.log_le_log hlogN0 h1
      rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) hlogx.ne'] at hh
      change Real.log (Real.log (N : ℝ)) ≤ 1+Real.log (Real.log x)
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)]
    have hratio : (N : ℝ)/Real.log N ≤ 3*x/((D : ℝ)*Real.log x) := by
      calc
        _ ≤ (2*x/D)/((9/10 : ℝ)*Real.log x) :=
          div_le_div₀ (by positivity) hNup (by positivity) hlogN
        _ ≤ _ := by field_simp; nlinarith
    calc
      _ ≤ ((nonNormalPrimes S N).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ C*N/Real.log N*(B N)^5*(Real.log S)^(-1/6 : ℝ) := hcount S hS N hN4
      _ ≤ (C*(3*x/((D : ℝ)*Real.log x)))*(1+B x)^5*(Real.log S)^(-1/6 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hE
        apply mul_le_mul
        · simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hratio hC.le
        · exact pow_le_pow_left₀ hBN0 hBN 5
        · positivity
        · positivity
      _ = _ := by ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero]
    positivity

end TotientAsymptotic

end

end OAI
