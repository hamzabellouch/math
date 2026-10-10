import OAI.NumberTheory.Jacobsthal.Primes.TagPrimePartition

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosStoppedTagSieve

open scoped BigOperators
open Erdos970Dependency.SiegelWalfisz

lemma inverse_totient_intersection (Q : ℕ) (T : Finset ℕ)
    (hT : ∀ t∈T,t.Prime) (hQT : ∀ t∈T,Q.Coprime t) :
    (1:ℝ)/((Q*(∏ t∈T,t)).totient:ℝ)=
      (1/(Q.totient:ℝ))*(∏ t∈T,1/((t:ℝ)-1)) := by
  rw [totient_intersection_modulus Q T hT hQT,Nat.cast_mul,Nat.cast_prod]
  have he : (∏ t∈T,((t-1:ℕ):ℝ))=∏ t∈T,((t:ℝ)-1) := by
    apply Finset.prod_congr rfl
    intro t ht
    rw [Nat.cast_sub (hT t ht).one_le,Nat.cast_one]
  rw [he]
  simp only [one_div,mul_inv_rev,Finset.prod_inv_distrib]
  ring

theorem intersection_prime_error :
    ∃ c C X₀ : ℝ,0 < c ∧ 0 < C ∧ 3 ≤ X₀ ∧
      ∀ R V : ℝ,X₀ ≤ R → 0 ≤ V → V ≤ R → ∀ Q : ℕ,0 < Q →
      ∀ T A : Finset ℕ,∀ rho : (t : ℕ) → ZMod t,
      (∀ t∈T,t.Prime) → (∀ t∈T,Q.Coprime t) →
      (∀ a∈A,a<Q) → (∀ a∈A,a.Coprime Q) → (∀ t∈T,rho t≠0) →
      (Q*(∏ t∈T,t):ℕ) ≤ Real.exp (c*cubeHeight R) →
      |((intersectionPrimes R V Q T A rho).card:ℝ)-
        (((intervalPrimes R V 1 0).card:ℝ)*(A.card:ℝ)/(Q.totient:ℝ))*(∏ t∈T,1/((t:ℝ)-1))| ≤
          (A.card:ℝ)*C*R*Real.exp (-c*cubeHeight R) := by
  obtain ⟨c,C,X₀,hc,hC,hX₀,hAP⟩ := interval_AP_count_error
  refine ⟨c,C,X₀,hc,hC,hX₀,?_⟩
  intro R V hR hV hVR Q hQ T A rho hT hQT hA hAc hrho hmod
  let B := intersectionResidues Q T A rho hT hQT
  let M := Q*(∏ t∈T,t)
  let N : ℝ := (intervalPrimes R V 1 0).card
  have hM : 0 < M := Nat.mul_pos hQ (Finset.prod_pos (fun t ht => (hT t ht).pos))
  have hB : B.card=A.card := intersectionResidues_card Q hQ T A rho hT hQT hA
  have hbound : ∀ a∈B,|((intervalPrimes R V M (a:ℤ)).card:ℝ)-N/(M.totient:ℝ)| ≤
      C*R*Real.exp (-c*cubeHeight R) := by
    intro a ha
    have hred := (intersectionResidues_reduced Q hQ T A rho hT hQT hA hAc hrho a ha).2
    exact hAP R V hR hV hVR M (a:ℤ) hM hred.isCoprime hmod
  have hmean : (∑ _a∈B,N/(M.totient:ℝ))=
      (N*(A.card:ℝ)/(Q.totient:ℝ))*(∏ t∈T,1/((t:ℝ)-1)) := by
    rw [Finset.sum_const,nsmul_eq_mul,hB]
    have hd := inverse_totient_intersection Q T hT hQT
    change 1/(M.totient:ℝ)=_ at hd
    calc
      _ = N*(A.card:ℝ)*(1/(M.totient:ℝ)) := by ring
      _ = _ := by rw [hd]; ring
  have hsum : (∑ a∈B,(((intervalPrimes R V M (a:ℤ)).card:ℝ)-N/(M.totient:ℝ)))=
      ((intersectionPrimes R V Q T A rho).card:ℝ)-
        (N*(A.card:ℝ)/(Q.totient:ℝ))*(∏ t∈T,1/((t:ℝ)-1)) := by
    rw [Finset.sum_sub_distrib,hmean,← Nat.cast_sum]
    congr 1
    exact_mod_cast (intersectionPrimes_card R V Q hQ T A rho hT hQT hA).symm
  change |((intersectionPrimes R V Q T A rho).card:ℝ)-
    (N*(A.card:ℝ)/(Q.totient:ℝ))*(∏ t∈T,1/((t:ℝ)-1))| ≤ _
  rw [← hsum]
  calc
    _ ≤ ∑ a∈B,|((intervalPrimes R V M (a:ℤ)).card:ℝ)-N/(M.totient:ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a∈B,C*R*Real.exp (-c*cubeHeight R) := Finset.sum_le_sum hbound
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,hB]; ring

end ErdosStoppedTagSieve


end Erdos970

end OAI
