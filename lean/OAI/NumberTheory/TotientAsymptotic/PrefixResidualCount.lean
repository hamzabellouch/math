import OAI.NumberTheory.TotientAsymptotic.FailedRowValueCount

namespace OAI

/-! Counting at any strict prime boundary with an admissible retained prefix. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem prefix_residual_value_count : ∃ C : ℝ,0 < C ∧
    ∀ᶠ x : ℝ in atTop,∀ j : ℕ,1 ≤ j → j ≤ m x →
    ∀ Q : Finset ℕ,∀ n : ℕ → ℕ,
    (∀ v ∈ Q,0 < n v ∧ (n v).totient=v ∧
      x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧ (v:ℝ) ≤ x ∧
      j ≤ (n v).primeFactorsList.length ∧ fordPrime (n v) j < fordPrime (n v) (j-1)) →
    (∀ v ∈ Q,j=1 ∨ ((∀ i,(fordPrefixPrimes (n v) (j-1) i).Prime) ∧
      primePrefixCoord (fordPrefixPrimes (n v) (j-1)) ∈
        enlargedSimplex (j-1) (B x) (xi x 0) (fun i => xi x (i.val+1)) ∧
      (∀ i,i.val+1=j-1 → (1/100:ℝ) ≤ primePrefixCoord (fordPrefixPrimes (n v) (j-1)) i))) →
    (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (j-1)*
      ∑ d ∈ Q.image (fun v => (fordCofactor (n v) j).totient),(d:ℝ)⁻¹ := by
  classical
  obtain ⟨A,hA,hmass⟩ := ford_unbanded_prime_mass
  refine ⟨64*(A+1),by positivity,?_⟩
  filter_upwards [hmass,large_prime_product_value_count,large_prime_totient_count,
    eventually_gt_atTop (1:ℝ),B_tendsto.eventually (eventually_gt_atTop (0:ℝ))]
    with x hx hcount hheadcount hx1 hB
  intro j hj hjm Q n hQ hprefix
  let P := Q.image (fun v => fordPrefixPrimes (n v) (j-1))
  let D := Q.image (fun v => (fordCofactor (n v) j).totient)
  have hD (d) (hd : d ∈ D) : 0 < d := by
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hd
    exact Nat.totient_pos.mpr (fordCofactor_pos _ _)
  have hnorm : 0 ≤ x/Real.log x := div_nonneg (by linarith) (Real.log_pos hx1).le
  have hsum : 0 ≤ ∑ d ∈ D,(d:ℝ)⁻¹ := Finset.sum_nonneg (fun _ _ => by positivity)
  by_cases hj1 : j=1
  · subst j
    have hh := hheadcount D Q hD (by
      intro v hv
      obtain ⟨hn,hφ,hlarge,hvx,hlen,_⟩ := hQ v hv
      refine ⟨n v,fordPrime (n v) 0,hn,hφ,fordPrime_prime (by omega),?_,hlarge,hvx,?_⟩
      · have he := fordCofactor_step (n v) 0
        rw [fordCofactor_zero hn] at he
        exact ⟨fordCofactor (n v) 1,he⟩
      · have he : n v/fordPrime (n v) 0=fordCofactor (n v) 1 := by
          simpa only [fordCofactor_zero hn,Nat.zero_add] using fordCofactor_div (n v) 0
        rw [he]
        exact Finset.mem_image.mpr ⟨v,hv,rfl⟩)
    have hcoef : 64*x/Real.log x ≤ 64*(A+1)*(x/Real.log x) := by
      calc
        _ = 64*(x/Real.log x) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hA]) hnorm
    have hb := hh.trans (mul_le_mul_of_nonneg_right hcoef hsum)
    simpa [G,D] using hb
  have hP (p) (hp : p ∈ P) : (∀ i,(p i).Prime) ∧
      primePrefixCoord p ∈ enlargedSimplex (j-1) (B x) (xi x 0) (fun i => xi x (i.val+1)) ∧
      (∀ i,i.val+1=j-1 → (1/100:ℝ) ≤ primePrefixCoord p i) := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hp
    exact (hprefix v hv).resolve_left hj1
  have hdim : m x-(m x-(j-1))=j-1 := Nat.sub_sub_self (by omega)
  have hPmass : (∑ p ∈ P,reciprocalShiftWeight p) ≤ (A+1)*G x (j-1) := by
    have hh := hx (m x-(j-1)) (by omega)
    rw [hdim] at hh
    exact (hh P hP).trans (mul_le_mul_of_nonneg_right (by linarith) (G_pos hB _).le)
  have hh := hcount (j-1) P D Q (fun p hp => (hP p hp).1) hD (by
    intro v hv
    obtain ⟨hn,hφ,hlarge,hvx,hlen,hgap⟩ := hQ v hv
    refine ⟨n v,fordPrime (n v) 0,hn,hφ,fordPrime_prime (by omega),?_,hlarge,hvx,?_⟩
    · have he := fordCofactor_step (n v) 0
      rw [fordCofactor_zero hn] at he
      exact ⟨fordCofactor (n v) 1,he⟩
    · apply Finset.mem_image.mpr
      refine ⟨(fordPrefixPrimes (n v) (j-1),(fordCofactor (n v) j).totient),
        Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨v,hv,rfl⟩,
          Finset.mem_image.mpr ⟨v,hv,rfl⟩⟩,?_⟩
      exact (strict_gap_residual_totient hn (by omega) hlen hgap).symm)
  have hcoef : 0 ≤ 64*x/Real.log x :=
    div_nonneg (by linarith only [hx1]) (Real.log_pos hx1).le
  apply hh.trans
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPmass hcoef) hsum
  convert hb using 1
  dsimp only [D]
  ring

end TotientAsymptotic

end

end OAI
