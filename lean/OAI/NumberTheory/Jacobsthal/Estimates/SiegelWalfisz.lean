import OAI.NumberTheory.Jacobsthal.Sieve.ResidueSqrtSplit

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter _root_.MeasureTheory
open scoped Topology
open ErdosPrimeInputs.PrimeCountAbel (logarithmicIntegral)

theorem siegel_walfisz_eventually (A M : ℝ) (hA : 0 < A) (hM : 0 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (r : ℤ),
      IsUnit (r:ZMod q) → (q:ℝ) ≤ (Real.log X)^A →
      |((intervalPrimes 0 X q r).card:ℝ)-logarithmicIntegral X/(q.totient:ℝ)| ≤
        C*X/(Real.log X)^M := by
  obtain ⟨K,hK,hθ⟩ := residueTheta_log_power (A+1) M (by linarith) hM
  obtain ⟨b,hb⟩ := eventually_atTop.mp hθ
  let D : ℝ := (Real.log 4+1)/(Real.log 2)^2
  let E : ℝ := 2/Real.log 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨E+K+D+K*(2:ℝ)^M,by positivity,?_⟩
  filter_upwards [Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (max 3 b)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2*(2:ℝ)^A)),
    eventually_sqrt_le_log_power M,eventually_log_rpow_le_self M] with X hs hlog hroot hpow
  intro q _ r hr hq
  have hs3 : 3 ≤ Real.sqrt X := (le_max_left _ _).trans hs
  have hsb : b ≤ Real.sqrt X := (le_max_right _ _).trans hs
  have hx3 : 3 ≤ X := hpow.1
  have hx0 : 0 < X := by linarith
  have hsX : Real.sqrt X ≤ X := by nlinarith [Real.sq_sqrt hx0.le]
  have hL1 : 1 ≤ Real.log X :=
    ((Real.lt_log_iff_exp_lt hx0).mpr (Real.exp_one_lt_three.trans_le hx3)).le
  have hL : 0 < Real.log X := by linarith
  have hscale : 1 ≤ X/(Real.log X)^M := (le_div_iff₀ (by positivity)).mpr (by simpa using hpow.2)
  have herror : ∀ t, Real.sqrt X ≤ t →
      |residueTheta (r:ZMod q) t-t/(q.totient:ℝ)| ≤ K*t/(Real.log t)^M := by
    intro t ht
    exact hb t (hsb.trans ht) q (r:ZMod q) hr
      (modulus_admissible_above_sqrt hA hs3 hlog ht hq)
  have hend : |(residueTheta (r:ZMod q) X-X/(q.totient:ℝ))/Real.log X| ≤
      K*X/(Real.log X)^M := by
    rw [abs_div,abs_of_pos hL]
    exact (div_le_div_of_nonneg_right (herror X hsX) hL.le).trans
      (div_le_self (by positivity) hL1)
  have hlo : |∫ t in 2..Real.sqrt X, residueErrorKernel (r:ZMod q) t| ≤
      D*X/(Real.log X)^M := by
    calc
      _ ≤ D*Real.sqrt X := residueErrorKernel_low_integral _ (by linarith)
      _ ≤ D*(X/(Real.log X)^M) := mul_le_mul_of_nonneg_left hroot hD.le
      _ = _ := by ring
  have hhi := residueErrorKernel_high_integral (r:ZMod q) hK.le hM hs3 herror
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (residueErrorKernel_integrable (r:ZMod q) (by norm_num) (by linarith : (2:ℝ)≤Real.sqrt X))
    (residueErrorKernel_integrable (r:ZMod q) (by linarith : (2:ℝ)≤Real.sqrt X) hsX)
  have hint : |∫ t in 2..X, residueErrorKernel (r:ZMod q) t| ≤
      D*X/(Real.log X)^M+(K*(2:ℝ)^M)*X/(Real.log X)^M := by
    rw [← hsplit]
    exact (abs_add_le _ _).trans (add_le_add hlo hhi)
  have hphi : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hconst : |2/((q.totient:ℝ)*Real.log 2)| ≤ E*X/(Real.log X)^M := by
    rw [abs_of_nonneg (by positivity)]
    calc
      _ = E/(q.totient:ℝ) := by dsimp [E]; ring
      _ ≤ E := div_le_self hE.le hphi
      _ ≤ E*(X/(Real.log X)^M) := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hscale hE.le
      _ = _ := by ring
  rw [intervalPrimes_error_eq (by linarith) q r]
  calc
    _ ≤ |2/((q.totient:ℝ)*Real.log 2)|+
        |(residueTheta (r:ZMod q) X-X/(q.totient:ℝ))/Real.log X|+
        |∫ t in 2..X, residueErrorKernel (r:ZMod q) t| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ E*X/(Real.log X)^M+K*X/(Real.log X)^M+
        (D*X/(Real.log X)^M+(K*(2:ℝ)^M)*X/(Real.log X)^M) :=
      add_le_add (add_le_add hconst hend) hint
    _ = _ := by ring

lemma isUnit_intCast_of_isCoprime {q : ℕ} {r : ℤ} (hr : IsCoprime r (q:ℤ)) :
    IsUnit (r:ZMod q) := by
  obtain ⟨u,v,huv⟩ := hr
  have hc : (u:ZMod q)*(r:ZMod q)+(v:ZMod q)*(q:ZMod q)=1 := by
    have h := congrArg (fun z:ℤ => (z:ZMod q)) huv
    push_cast at h
    exact h
  simp only [ZMod.natCast_self,mul_zero,add_zero] at hc
  apply isUnit_of_dvd_one
  exact ⟨(u:ZMod q),by simpa only [mul_comm] using hc.symm⟩

theorem siegel_walfisz (A M : ℝ) (hA : 0 < A) (hM : 0 < M) :
    ∃ C X₀ : ℝ, 0 < C ∧ 3 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ (q : ℕ) (r : ℤ), 0 < q → IsCoprime r (q:ℤ) →
      (q:ℝ) ≤ (Real.log X)^A →
      |((intervalPrimes 0 X q r).card:ℝ)-logarithmicIntegral X/(q.totient:ℝ)| ≤
        C*X/(Real.log X)^M := by
  obtain ⟨C,hC,h⟩ := siegel_walfisz_eventually A M hA hM
  obtain ⟨b,hb⟩ := eventually_atTop.mp h
  refine ⟨C,max 3 b,hC,le_max_left _ _,?_⟩
  intro X hX q r hq hr hbound
  let _ : NeZero q := ⟨hq.ne'⟩
  exact hb X ((le_max_right _ _).trans hX) q r (isUnit_intCast_of_isCoprime hr) hbound

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
