import OAI.NumberTheory.TotientAsymptotic.TerminalBandCount

namespace OAI

/-! Retain an arbitrary restriction on the prime prefix while counting a
terminal strip through its distinct residual totients. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem terminal_prefix_mass_count : ∃ D : ℝ,0 < D ∧
    ∀ᶠ x : ℝ in atTop,∀ K k : ℕ,∀ Q : Finset ℕ,∀ n : ℕ → ℕ,
    (∀ v∈Q,0 < n v ∧ (n v).totient=v ∧
      x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧ (v:ℝ) ≤ x ∧
      K+1 ≤ (n v).primeFactorsList.length ∧
      fordPrime (n v) (K+1) < fordPrime (n v) K ∧
      fordPrimeCoordinate (n v) (K+1) ≤ (k:ℝ)+1) →
    (Q.card:ℝ) ≤ D*(x/Real.log x)*
      (∑ p∈Q.image (fun v => fordPrefixPrimes (n v) K),reciprocalShiftWeight p)*
      Real.exp (10*(Real.log ((k:ℝ)+5))^2) := by
  obtain ⟨D,hD,hres⟩ := smooth_terminal_mass_bound
  refine ⟨64*D,by positivity,?_⟩
  filter_upwards [large_prime_product_value_count,eventually_gt_atTop (1:ℝ)]
    with x hx hx1
  intro K k Q n hQ
  let P := Q.image (fun v => fordPrefixPrimes (n v) K)
  let R := Q.image (fun v => (fordCofactor (n v) (K+1)).totient)
  have hRpos (d) (hd : d∈R) : 0 < d := by
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hd
    exact Nat.totient_pos.mpr (fordCofactor_pos _ _)
  have hRmass : (∑ d∈R,(d:ℝ)⁻¹) ≤ D*Real.exp (10*(Real.log ((k:ℝ)+5))^2) := by
    apply hres k (by positivity) R
    intro d hd
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hd
    exact ⟨⟨fordCofactor (n v) (K+1),fordCofactor_pos _ _,rfl⟩,
      small_terminal_smooth (by positivity) (hQ v hv).2.2.2.2.2.2⟩
  have hh := hx K P R Q (by
    intro p hp i
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hp
    apply fordPrime_prime
    have hlen := (hQ v hv).2.2.2.2.1
    have := i.isLt
    omega) hRpos (by
    intro v hv
    obtain ⟨hn,hφ,hhead,hvx,hlen,hgap,_⟩ := hQ v hv
    refine ⟨n v,fordPrime (n v) 0,hn,hφ,fordPrime_prime (by omega),?_,hhead,hvx,?_⟩
    · have he := fordCofactor_step (n v) 0
      rw [fordCofactor_zero hn] at he
      exact ⟨fordCofactor (n v) 1,he⟩
    · apply Finset.mem_image.mpr
      refine ⟨(fordPrefixPrimes (n v) K,(fordCofactor (n v) (K+1)).totient),
        Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨v,hv,rfl⟩,
          Finset.mem_image.mpr ⟨v,hv,rfl⟩⟩,?_⟩
      have he := (strict_gap_residual_totient (n:=n v) (j:=K+1) hn (by omega) hlen hgap).symm
      change (fordCofactor (n v) (K+1)).totient *
        (∏ i : Fin K,fordPrime (n v) (i.val+1)).totient = _
      rw [Fin.prod_univ_eq_prod_range (fun i => fordPrime (n v) (i+1))] at he ⊢
      simpa only [Nat.add_sub_cancel] using he)
  apply hh.trans
  have hcoef : 0 ≤ (64*x/Real.log x)*(∑ p∈P,reciprocalShiftWeight p) :=
    mul_nonneg (div_nonneg (by positivity) (Real.log_pos hx1).le)
      (Finset.sum_nonneg (fun p _ => reciprocalShiftWeight_nonneg p))
  have hh' := mul_le_mul_of_nonneg_left hRmass hcoef
  convert hh' using 1; dsimp only [P]; ring

end TotientAsymptotic

end

end OAI
