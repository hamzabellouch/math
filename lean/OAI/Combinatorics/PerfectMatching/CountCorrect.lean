import OAI.Combinatorics.PerfectMatching.Completion

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset MatchingEntropy

lemma zero_test (G : Input) (hn : 4 ≤ G.n) (heven : Even G.n) :
    R G < -10*(G.n:ℤ) ↔ count G = 0 := by
  have hp := R_partition_bracket G hn heven
  have hc := completion_bracket G hn heven
  have hn' : (4:ℝ) ≤ G.n := by exact_mod_cast hn
  constructor
  · intro hr
    by_contra hN
    have hNpos : 0 < count G := Nat.pos_of_ne_zero hN
    have hz : 0 ≤ logZ G := by
      unfold logZ
      exact div_nonneg (Real.log_nonneg (hc.2 hNpos).1) log_two_pos.le
    have hr' : (R G:ℝ) < -10*(G.n:ℝ) := by exact_mod_cast hr
    linarith [hp.2]
  · intro hN
    have hz := hc.1 hN
    have hr' : (R G:ℝ) < -10*(G.n:ℝ) := by linarith [hp.1]
    exact_mod_cast hr'

lemma log_count_bracket (G : Input) (hn : 4 ≤ G.n) (heven : Even G.n)
    (hN : 0 < count G) :
    (R G:ℝ)-5*(G.n:ℝ) ≤ Real.log (count G)/Real.log 2 ∧
      Real.log (count G)/Real.log 2 ≤ (R G:ℝ)+4*(G.n:ℝ) := by
  have hp := R_partition_bracket G hn heven
  obtain ⟨_hone,hlo,hhi⟩ := (completion_bracket G hn heven).2 hN
  have hN' : (0:ℝ) < count G := by exact_mod_cast hN
  have hn' : (4:ℝ) ≤ G.n := by exact_mod_cast hn
  have hlo' := Real.log_le_log (show (0:ℝ) < 2⁻¹^(G.n/2)*(count G:ℝ) by positivity) hlo
  have hhi' := Real.log_le_log (Z_pos G hn heven) hhi
  rw [Real.log_mul (by positivity) hN'.ne',Real.log_pow,Real.log_inv] at hlo'
  rw [Real.log_mul (by norm_num) hN'.ne'] at hhi'
  have hdiv : ((G.n/2:ℕ):ℝ) ≤ (G.n:ℝ) := by exact_mod_cast Nat.div_le_self G.n 2
  dsimp only [logZ] at hp
  constructor
  · apply (le_div_iff₀ log_two_pos).2
    have hpart := (le_div_iff₀ log_two_pos).1 hp.1
    nlinarith [log_two_pos]
  · apply (div_le_iff₀ log_two_pos).2
    have hpart := (div_le_iff₀ log_two_pos).1 hp.2
    nlinarith [mul_le_mul_of_nonneg_right hdiv log_two_pos.le]

theorem estimate_correct (G : Input) (hn : 4 ≤ G.n) (heven : Even G.n) :
    estimate G ≤ count G ∧ count G ≤ 2^(9*G.n)*estimate G ∧
      (estimate G=0 ↔ count G=0) := by
  by_cases hN : count G=0
  · have hr : R G < -(10*(G.n:ℤ)) := by simpa only [neg_mul] using (zero_test G hn heven).2 hN
    simp [estimate,hr,hN]
  · have hNpos : 0 < count G := Nat.pos_of_ne_zero hN
    have hr : ¬R G < -(10*(G.n:ℤ)) := by simpa only [←neg_mul,zero_test G hn heven] using hN
    have he : estimate G=2^(R G-5*(G.n:ℤ)).toNat := by simp [estimate,hr]
    let rho := (R G-5*(G.n:ℤ)).toNat
    have he' : estimate G=2^rho := he
    have hrhol : (R G:ℝ)-5*(G.n:ℝ) ≤ (rho:ℝ) := by
      have hi : R G-5*(G.n:ℤ) ≤ (rho:ℤ) := Int.self_le_toNat _
      exact_mod_cast hi
    have hNc : (0:ℝ) < count G := by exact_mod_cast hNpos
    have hN1 : (1:ℝ) ≤ count G := by exact_mod_cast hNpos
    have hlog0 : 0 ≤ Real.log (count G)/Real.log 2 :=
      div_nonneg (Real.log_nonneg hN1) log_two_pos.le
    have hbracket := log_count_bracket G hn heven hNpos
    have hrhou : (rho:ℝ) ≤ Real.log (count G)/Real.log 2 := by
      by_cases hnon : 0 ≤ R G-5*(G.n:ℤ)
      · have hh : (rho:ℤ)=R G-5*(G.n:ℤ) := Int.toNat_of_nonneg hnon
        have hh' : (rho:ℝ)=(R G:ℝ)-5*(G.n:ℝ) := by exact_mod_cast hh
        rw [hh']; exact hbracket.1
      · have hz : rho=0 := Int.toNat_of_nonpos (by omega)
        simpa only [hz,Nat.cast_zero] using hlog0
    have hlow : (2:ℝ)^rho ≤ (count G:ℝ) := by
      apply (Real.log_le_log_iff (by positivity) hNc).1
      rw [Real.log_pow]
      exact (le_div_iff₀ log_two_pos).1 hrhou
    have hupp : (count G:ℝ) ≤ (2:ℝ)^(9*G.n)*(2:ℝ)^rho := by
      apply (Real.log_le_log_iff hNc (by positivity)).1
      rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow]
      have hh : Real.log (count G)/Real.log 2 ≤ (9*G.n:ℕ)+(rho:ℝ) := by
        push_cast; linarith [hbracket.2]
      have hh' := (div_le_iff₀ log_two_pos).1 hh
      push_cast at hh' ⊢
      nlinarith
    have hlow' : 2^rho ≤ count G := by exact_mod_cast hlow
    have hupp' : count G ≤ 2^(9*G.n)*2^rho := by exact_mod_cast hupp
    rw [he']
    refine ⟨hlow',hupp',?_⟩
    simp [hN]

end
end BinaryMatching.Algorithm
end

end OAI
