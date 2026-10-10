import OAI.NumberTheory.TotientAsymptotic.LocalValueNormality
import OAI.NumberTheory.TotientAsymptotic.ResidualDyadicMass

namespace OAI

/-! The actual nonnormal-witness counts summed over residual dyadic layers. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem local_nonnormal_witness_mass_rate {A : ℝ} (hA : 0 ≤ A) (K : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀ (d q L : ℕ),0 < d →
      ∀ (R Q : Finset ℕ) (F : ℕ → ℕ),Q ⊆ R →
      (∀ r ∈ Q,1 < d*r.totient ∧ ((d*r.totient:ℕ):ℝ) ≤ (2:ℝ)^L) →
      (∀ r ∈ Q,let z := (2:ℝ)^(Nat.clog 2 (d*r.totient));
        256 ≤ z ∧ 0 ≤ B z ∧ Real.log (B z+4) ≤ A*h) →
      (∀ r ∈ R,∀ p : ℕ,p.Prime → p ∣ r → IsNormalPrime (localNormalityScale h) p) →
      (∀ p : ℕ,p.Prime → p ∣ q → IsNormalPrime (localNormalityScale h) p) →
      (∀ r ∈ R,(∃ s ∈ R,s≠r ∧ s.totient=r.totient) → ∃ s ∈ R,F r=s*q) →
      (∀ r ∈ Q,∃ p : ℕ,p.Prime ∧ p ∣ F r ∧ ¬IsNormalPrime (localNormalityScale h) p) →
      (∀ r ∈ Q,0<F r ∧ (F r).totient=d*r.totient) →
      (∑ r ∈ Q,(r.totient:ℝ)⁻¹) ≤
        (4*d/Real.log 2)*rho^(K*h)*(1+Real.log L) := by
  classical
  filter_upwards [local_nonnormal_witness_count_rate hA K] with h hc
  intro d q L hd R Q F hQR hrange hlocal hR hq hbranch hbad hF
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA' : 0 ≤ rho^(K*h)/Real.log 2 := div_nonneg (pow_pos rho_pos _).le hlog2.le
  have hcount (k : ℕ) (hk : k ∈ Finset.Icc 1 L) :
      ((Q.filter (fun r => Nat.clog 2 (d*r.totient)=k)).card:ℝ) ≤
        (rho^(K*h)/Real.log 2)*(2:ℝ)^k/k := by
    let T := Q.filter (fun r => Nat.clog 2 (d*r.totient)=k)
    by_cases hQ : T.Nonempty
    · obtain ⟨r,hr⟩ := hQ
      have hkr := (Finset.mem_filter.mp hr).2
      have hz := hlocal r (Finset.mem_filter.mp hr).1
      dsimp only at hz
      rw [hkr] at hz
      have hbound := hc ((2:ℝ)^k) d q hz.1 hz.2.1 hz.2.2 hd R T F
        (fun r hr => hQR (Finset.mem_filter.mp hr).1) hR hq hbranch
        (fun r hr => hbad r (Finset.mem_filter.mp hr).1) (by
          intro r hr
          obtain ⟨hr,he⟩ := Finset.mem_filter.mp hr
          refine ⟨(hF r hr).1,(hF r hr).2,?_⟩
          have hh := (dyadic_nat_bounds (hrange r hr).1).2.2
          rwa [he] at hh)
      apply hbound.trans_eq
      rw [dyadic_endpoint_log]
      ring
    · have he : T=∅ := Finset.not_nonempty_iff_eq_empty.mp hQ
      change (T.card:ℝ) ≤ _
      rw [he]
      simp only [Finset.card_empty,Nat.cast_zero]
      positivity
  have hm := residual_dyadic_mass Q d L hA' hrange hcount
  apply hm.trans_eq
  ring

end TotientAsymptotic

end

end OAI
