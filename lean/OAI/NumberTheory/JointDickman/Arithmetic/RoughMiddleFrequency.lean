import OAI.NumberTheory.JointDickman.Arithmetic.RoughPhaseScales

namespace OAI

/-! # Uniform middle-frequency cancellation for rough multiplicative weights -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology

/-- The prime-power support is literal: below the cutoff the function is
one outside primes exceeding `N^c`. This covers the auxiliary count masks.
No uniform short-interval theorem is used. -/
theorem rough_middle_frequency {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (P : Finset ℕ) (F : ℕ → ℂ),
      (∀ p ∈ P, p.Prime ∧ (N:ℝ)^c < (p:ℝ) ∧ (p:ℝ) ≤ N) →
      F 1 = 1 → Multiplicative F → OneBounded F →
      (∀ p k : ℕ, p.Prime → p ∉ P → p^k ≤ N → F (p^k) = 1) →
      ∀ t : ℝ, (Real.log N)^((1:ℝ)/16) ≤ |t| → |t| ≤ 4*(Real.log N)^8 →
      ‖halaszPhaseMean F t N‖/(N:ℝ) ≤ ε := by
  obtain ⟨C,hC,hbound⟩ := rough_phase_mean_bound
  let M : ℝ := -Real.log c+1
  let J : ℕ := ⌈1/c⌉₊
  have hM : 0 ≤ M := by
    have hh := Real.log_nonpos hc.le hc1
    dsimp [M]
    linarith
  have hbudget := ((rough_phase_budget_tendsto c M C hc J).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_le_nhds hε)
  have hscales := tendsto_natCast_atTop_atTop.eventually rough_logarithmic_cutoff
  have hmass := tendsto_natCast_atTop_atTop.eventually (rough_prime_mass_bounded hc hc1)
  have hpower := (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  filter_upwards [hbudget,hscales,hmass,hpower.eventually (eventually_ge_atTop 2)]
    with N hbudgetN hs hm hpow
  intro P F hP hF1 hFm hFb hlocal t htlo hthi
  have hN : 0 < N := by exact_mod_cast (show (0:ℝ) < N by linarith [hs.1])
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hN
  have hl : 0 < Real.log N := by linarith [hs.2.1]
  let Y : ℝ := (N:ℝ)/(Real.log N)^10
  let K : ℕ := ⌊(N:ℝ)^c⌋₊
  have hK : K ≠ 0 := by
    have hh : 2 ≤ K := Nat.le_floor hpow
    omega
  have hmass0 : 0 ≤ ∑ p ∈ P, 1/(p:ℝ) := sum_nonneg (fun _ _ => by positivity)
  have hmassM : (∑ p ∈ P, 1/(p:ℝ)) ≤ M := hm P hP
  have hcard : ∀ D ∈ P.powerset, (∏ p ∈ D, (p:ℝ)) ≤ N → D.card ≤ J := by
    intro D hD hDN
    exact power_lower_subset_card hs.1 hc D
      (fun p hp => (hP p (mem_powerset.mp hD hp)).2.1.le) hDN
  have hb := hbound P F t ((N:ℝ)^c) Y N J K hN hK hpow hs.2.2.1 hs.2.2.2.1
    (fun p hp => ⟨(hP p hp).1,(hP p hp).2.1,
      (Nat.floor_lt (Real.rpow_nonneg hNr.le c)).mpr (hP p hp).2.1⟩)
    hF1 hFm hFb hlocal hcard
  have hnear : 2/(1+|t|) ≤ 2*(Real.log N)^(-(1:ℝ)/16) := by
    have hp : 0 < (Real.log N)^((1:ℝ)/16) := Real.rpow_pos_of_pos hl _
    rw [show -(1:ℝ)/16 = -(1/16:ℝ) by ring,Real.rpow_neg hl.le,← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (by norm_num) hp (by linarith [abs_nonneg t])
  have hloss := rough_cutoff_phase_loss hNr hs.2.1 hthi
  have hfirst : (2/(1+|t|)+9*(1+|t|)*Y/N) ≤
      2*(Real.log N)^(-(1:ℝ)/16)+45/(Real.log N)^2 := by
    have h9 : 9*(1+|t|)*Y/N ≤ 45/(Real.log N)^2 := by
      calc
        _ = 9*((1+|t|)*((N:ℝ)/(Real.log N)^10)/N) := by dsimp [Y]; ring
        _ ≤ 9*(5/(Real.log N)^2) := mul_le_mul_of_nonneg_left hloss (by norm_num)
        _ = _ := by ring
    exact add_le_add hnear h9
  have hexp : Real.exp (2*∑ p ∈ P, 1/(p:ℝ)) ≤ Real.exp (2*M) :=
    Real.exp_le_exp.mpr (by linarith)
  have hsum : (∑ h ∈ range J, (∑ p ∈ P, 1/(p:ℝ))^h) ≤ ∑ h ∈ range J, M^h :=
    sum_le_sum (fun h _ => pow_le_pow_left₀ hmass0 hmassM h)
  have hratio : (Real.log ((N:ℝ)/Y)+C)/Real.log ((N:ℝ)^c) =
      (10*Real.log (Real.log N)+C)/(c*Real.log N) := by
    rw [Real.log_rpow hNr]
    dsimp [Y]
    rw [hs.2.2.2.2]
  have hratio0 : 0 ≤ (10*Real.log (Real.log N)+C)/(c*Real.log N) :=
    div_nonneg (by have := Real.log_nonneg hs.2.1; positivity) (mul_pos hc hl).le
  rw [hratio] at hb
  apply hb.trans
  apply le_trans _ hbudgetN
  exact add_le_add
    (add_le_add (mul_le_mul hfirst hexp (Real.exp_pos _).le (by positivity))
      (mul_le_mul_of_nonneg_left hsum (mul_nonneg (by positivity) hratio0))) le_rfl

/-- The application can specify the small-prime powers directly, without
choosing a finite support set. -/
theorem rough_middle_frequency_small_primes {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ F : ℕ → ℂ,
      F 1 = 1 → Multiplicative F → OneBounded F →
      (∀ p k : ℕ, p.Prime → (p:ℝ) ≤ (N:ℝ)^c → p^k ≤ N → F (p^k) = 1) →
      ∀ t : ℝ, (Real.log N)^((1:ℝ)/16) ≤ |t| → |t| ≤ 4*(Real.log N)^8 →
      ‖halaszPhaseMean F t N‖/(N:ℝ) ≤ ε := by
  classical
  filter_upwards [rough_middle_frequency hc hc1 hε] with N hN
  intro F hF1 hFm hFb hlocal t htlo hthi
  apply hN (largePrimeSet N ((N:ℝ)^c)) F _ hF1 hFm hFb _ t htlo hthi
  · intro p hp
    obtain ⟨hp,hl⟩ := mem_filter.mp hp
    obtain ⟨hpN,hp⟩ := Nat.mem_primesLE.mp hp
    exact ⟨hp,hl,by exact_mod_cast hpN.trans_eq (Nat.floor_natCast N)⟩
  · intro p k hp hpP hpk
    by_cases hk : k = 0
    · simpa [hk] using hF1
    have hpN : p ≤ N := (le_self_pow hp.one_le hk).trans hpk
    have hsmall : (p:ℝ) ≤ (N:ℝ)^c := by
      by_contra h
      apply hpP
      exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨by simpa using hpN,hp⟩,lt_of_not_ge h⟩
    exact hlocal p k hp hsmall hpk

end JointDickman

end OAI
