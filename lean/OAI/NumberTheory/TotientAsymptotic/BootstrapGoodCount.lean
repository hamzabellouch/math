import OAI.NumberTheory.TotientAsymptotic.BootstrapGoodValues
import OAI.NumberTheory.TotientAsymptotic.BootstrapLargeHead
import OAI.NumberTheory.TotientAsymptotic.BootstrapResidualMass

namespace OAI

/-! Count the surviving values by a large leading prime and smaller residual values. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem bootstrap_good_count : ∃ C : ℝ,0 < C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ J : ℕ,1 ≤ J → Real.exp ((Real.log x)^(81/100:ℝ)) ≤ (2:ℝ)^J →
    ∀ Q : Finset ℕ,(∀ v ∈ Q,IsTotient v ∧ BootstrapGood x v ∧
      x^(3/4:ℝ) < (v:ℝ) ∧ (v:ℝ) ≤ x) →
    (Q.card:ℝ) ≤ C*(x/Real.log x)*(1+B x)*dyadicTotientEnvelope J*(1+Real.log J) := by
  classical
  obtain ⟨C,hC,hmass⟩ := bootstrap_residual_mass
  refine ⟨64*C,by positivity,?_⟩
  filter_upwards [large_prime_totient_count,bootstrap_cofactor_size,
    bootstrap_residual_quarter,eventually_ge_atTop (Real.exp (Real.exp 1)),
    eventually_gt_atTop (1:ℝ)] with x hcount hsize hquarter hx hx1
  intro J hJ hY Q hQ
  let M := totientValues ((2:ℝ)^J)
  let P := Nat.primesLE ⌊2*x^2⌋₊
  let R := singlePrimeExtensions P M
  have hM : ∀ m ∈ M,IsTotient m ∧ (m:ℝ) ≤ (2:ℝ)^J := by
    intro m hm
    obtain ⟨hm,hmt⟩ := Finset.mem_filter.mp hm
    exact ⟨hmt,(Nat.cast_le.mpr (Finset.mem_Icc.mp hm).2).trans (Nat.floor_le (by positivity))⟩
  have hR : ∀ d ∈ R,0 < d := singlePrimeExtensions_pos
    (fun p hp => (Nat.mem_primesLE.mp hp).2) (fun m hm => isTotient_pos (hM m hm).1)
  have hcover : ∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
      x^(1/4:ℝ) ≤ p ∧ (v:ℝ) ≤ x ∧ (n/p).totient ∈ R := by
    intro v hv
    obtain ⟨ht,hgood,hvlo,hvhi⟩ := hQ v hv
    obtain ⟨n,hn,hφ⟩ := ht
    have hΩ : (n.totient.primeFactorsList.length:ℝ) ≤ 5*B x := by
      rw [hφ]
      exact hgood.1.1
    have hs := hsize n hn hΩ (hgood.2 n hn hφ)
    have hp := quarter_prime_of_residual hx1 hn (hs.trans hquarter) (by rwa [hφ])
    have hprime := quarter_fordPrime_prime hx1 hp
    have hpn : fordPrime n 0 ∣ n := by
      refine ⟨fordPrime n 1*fordCofactor n 2,?_⟩
      exact (ford_first_two_factorization hn).trans (mul_assoc _ _ _)
    have hres : (n/fordPrime n 0).totient ∈ R := by
      have hd : n/fordPrime n 0=fordCofactor n 1 := by
        calc
          n/fordPrime n 0 = fordCofactor n 0/fordPrime n 0 := by rw [fordCofactor_zero hn]
          _ = _ := fordCofactor_div n 0
      rw [hd]
      apply cofactor_singlePrimeExtensions
      · have hmpos := Nat.totient_pos.mpr (fordCofactor_pos n 2)
        have hmle : ((fordCofactor n 2).totient:ℝ) ≤ (2:ℝ)^J :=
          (Nat.cast_le.mpr (Nat.totient_le _)).trans (hs.trans hY)
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hmpos,Nat.le_floor hmle⟩,
          ⟨fordCofactor n 2,fordCofactor_pos n 2,rfl⟩⟩
      · intro hp1
        apply Nat.mem_primesLE.mpr
        refine ⟨Nat.le_floor ?_,hp1⟩
        have hnBound : (n:ℝ) ≤ 2*x^2 := by
          have hnφ : (n:ℝ) ≤ 2*(n.totient:ℝ)^2 := by exact_mod_cast totient_preimage_quadratic hn
          have hv0 : (0:ℝ) ≤ v := Nat.cast_nonneg _
          rw [hφ] at hnφ
          exact hnφ.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv0 hvhi 2) (by norm_num))
        exact (Nat.cast_le.mpr (fordPrime_le_self hn 1)).trans hnBound
    exact ⟨n,fordPrime n 0,hn,hφ,hprime,hpn,hp,hvhi,hres⟩
  have hh := hcount R Q hR hcover
  have hm := hmass x hx J hJ M hM
  have hlog : 0 < Real.log x := Real.log_pos hx1
  calc
    _ ≤ (64*x/Real.log x)*(∑ d ∈ R,(d:ℝ)⁻¹) := hh
    _ ≤ (64*x/Real.log x)*(C*(1+B x)*dyadicTotientEnvelope J*(1+Real.log J)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
