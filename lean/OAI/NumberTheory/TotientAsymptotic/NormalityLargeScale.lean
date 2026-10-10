import OAI.NumberTheory.TotientAsymptotic.FullOmegaTail
import OAI.NumberTheory.TotientAsymptotic.PublishedNormality

namespace OAI

/-! Large S makes interval normality vacuous, leaving the full factor-count tail. -/
noncomputable section
namespace TotientAsymptotic

lemma nonnormal_full_factor_excess {S : ℝ} {p N : ℕ} (hp : p.Prime) (hpN : p ≤ N)
    (hSN : (N:ℝ) ≤ S) (hbad : ¬IsNormalPrime S p) :
    2*B S ≤ ((p-1).primeFactorsList.length:ℝ) := by
  have hsmall : ¬(omegaIn (p-1) 1 S:ℝ) ≤ 2*B S := by
    intro hs
    apply hbad
    refine ⟨hp,hs,?_⟩
    intro U T hSU hUT hT
    have hpm : ((p-1:ℕ):ℝ) < N := by exact_mod_cast (show p-1 < N by have := hp.two_le; omega)
    linarith
  have hcount : omegaIn (p-1) 1 S ≤ (p-1).primeFactorsList.length := List.length_filter_le _ _
  have hcountR : (omegaIn (p-1) 1 S:ℝ) ≤ (p-1).primeFactorsList.length := by exact_mod_cast hcount
  linarith

 theorem normality_large_scale : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 2 < S →
    ∀ N : ℕ, 3 < N → 1 ≤ B N → (Real.log N)^6 ≤ Real.log S →
    ((nonNormalPrimes S N).card:ℝ) ≤
      C*N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ) := by
  classical
  obtain ⟨C,hC,hfull⟩ := full_factor_tail_mass
  refine ⟨C,hC,?_⟩
  intro S hS N hN hB hSlarge
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogS : 0 < Real.log S := Real.log_pos (by linarith)
  have hBS : 6*B N ≤ B S := by
    have hh := Real.log_le_log (pow_pos hlog 6) hSlarge
    simpa only [Real.log_pow,B,Nat.cast_ofNat] using hh
  have hSN : (N:ℝ) ≤ S := by
    have hb : B N ≤ B S := by linarith
    have hl := (Real.log_le_log_iff hlog hlogS).mp hb
    exact (Real.log_le_log_iff hN0 (by linarith : 0 < S)).mp hl
  let Q : Finset ℕ := (nonNormalPrimes S N).image (fun p => p-1)
  have hcard : Q.card = (nonNormalPrimes S N).card := by
    apply Finset.card_image_iff.mpr
    intro p hp r hr he
    change p-1=r-1 at he
    have hp2 := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2.two_le
    have hr2 := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hr).1).2.two_le
    omega
  have hb := hfull S (by linarith) N (by omega) (by linarith) hBS Q (by
    intro n hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hp,hbad⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpN,hprime⟩ := Nat.mem_primesLE.mp hp
    exact ⟨by have := hprime.two_le; omega,by omega,nonnormal_full_factor_excess hprime hpN hSN hbad⟩)
  rw [hcard] at hb
  apply hb.trans
  have hpow : 1 ≤ (B N)^5 := one_le_pow₀ hB
  have hrpow : 0 < (Real.log S)^(-1/6:ℝ) := Real.rpow_pos_of_pos hlogS _
  have hh := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ C*N/Real.log N*(Real.log S)^(-1/6:ℝ) by positivity)
  nlinarith

end TotientAsymptotic

end

end OAI
