import OAI.NumberTheory.TotientAsymptotic.PrimeExtensionCount

namespace OAI

/-! Exact coverage of large-prime totients by their residual totient values. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma totient_prime_extension_cases {n p : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    n.totient=(p-1)*(n/p).totient ∨ n.totient=p*(n/p).totient := by
  have he : p*(n/p)=n := Nat.mul_div_cancel' hpn
  by_cases hd : p ∣ n/p
  · right
    conv_lhs => rw [← he]
    exact Nat.totient_mul_of_prime_of_dvd hp hd
  · left
    conv_lhs => rw [← he]
    exact Nat.totient_mul_of_prime_of_not_dvd hp hd

lemma totient_mem_primeExtensionValues {x : ℝ} {n p : ℕ}
    (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n) (hpx : x^(1/4:ℝ) ≤ p)
    (hx : (n.totient:ℝ) ≤ x) :
    n.totient ∈ primeExtensionValues x (n/p).totient := by
  have hq : 0 < n/p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
  have hd : 0 < (n/p).totient := Nat.totient_pos.mpr hq
  have hcases := totient_prime_extension_cases hp hpn
  have hsize : (((p-1)*(n/p).totient:ℕ):ℝ) ≤ x := by
    rcases hcases with h|h
    · rwa [← h]
    · exact (Nat.cast_le.mpr (Nat.mul_le_mul_right (n/p).totient (Nat.sub_le p 1))).trans (by rwa [← h])
  apply Finset.mem_biUnion.mpr
  refine ⟨p,(mem_quarterPrimes hd).mpr ⟨hp,hpx,hsize⟩,?_⟩
  rcases hcases with h|h <;> simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto

/-- The residual set consists of values, so repeated preimages incur no extra factor. -/
theorem large_prime_totient_count : ∀ᶠ x : ℝ in atTop,
    ∀ R Q : Finset ℕ,(∀ d ∈ R,0 < d) →
    (∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
      x^(1/4:ℝ) ≤ p ∧ (v:ℝ) ≤ x ∧ (n/p).totient ∈ R) →
    (Q.card:ℝ) ≤ (64*x/Real.log x)*(∑ d ∈ R,(d:ℝ)⁻¹) := by
  classical
  filter_upwards [prime_extension_count_upper] with x hx
  intro R Q hR hQ
  have hsub : Q ⊆ R.biUnion (primeExtensionValues x) := by
    intro v hv
    obtain ⟨n,p,hn,he,hp,hpn,hpx,hvx,hr⟩ := hQ v hv
    refine Finset.mem_biUnion.mpr ⟨(n/p).totient,hr,?_⟩
    rw [← he]
    exact totient_mem_primeExtensionValues hn hp hpn hpx (by rwa [he])
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hx R hR)

end TotientAsymptotic

end

end OAI
