import OAI.NumberTheory.TotientAsymptotic.NonNormalExtensionCount
import OAI.NumberTheory.TotientAsymptotic.TotientCountingEnvelope

namespace OAI

/-! Distinct exceptional totient values, grouped by the residual value. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def abnormalExtensionPrimes (S x : ℝ) (d : ℕ) : Finset ℕ :=
  (quarterPrimes x d).filter (fun p => 4 ≤ p ∧ ¬IsNormalPrime S p)

def abnormalExtensionValues (S x : ℝ) (d : ℕ) : Finset ℕ :=
  (abnormalExtensionPrimes S x d).biUnion (fun p => {(p-1)*d,p*d})

lemma abnormal_extension_values_card (S x : ℝ) (d : ℕ) :
    (abnormalExtensionValues S x d).card ≤ 2*(abnormalExtensionPrimes S x d).card := by
  classical
  calc
    _ ≤ ∑ _p ∈ abnormalExtensionPrimes S x d,({(0:ℕ),1}:Finset ℕ).card :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun p _ => by simp; exact Finset.card_insert_le _ _))
    _ = _ := by simp; omega

lemma totient_mem_abnormalExtensionValues {S x : ℝ} {n p : ℕ}
    (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n) (hp4 : 4 ≤ p)
    (hpx : x^(1/4:ℝ) ≤ p) (hx : (n.totient:ℝ) ≤ x) (hbad : ¬IsNormalPrime S p) :
    n.totient ∈ abnormalExtensionValues S x (n/p).totient := by
  classical
  have hd : 0 < (n/p).totient := Nat.totient_pos.mpr
    (Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos)
  have hsize : (((p-1)*(n/p).totient:ℕ):ℝ) ≤ x := by
    rcases totient_prime_extension_cases hp hpn with h|h
    · rwa [← h]
    · exact (Nat.cast_le.mpr (Nat.mul_le_mul_right (n/p).totient (Nat.sub_le p 1))).trans (by rwa [← h])
  refine Finset.mem_biUnion.mpr ⟨p,Finset.mem_filter.mpr
    ⟨(mem_quarterPrimes hd).mpr ⟨hp,hpx,hsize⟩,hp4,hbad⟩,?_⟩
  rcases totient_prime_extension_cases hp hpn with h|h <;>
    simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto

/-- Large non-normal prime divisors cost only the reciprocal mass of the
residual totient values, even when a value has many preimages. -/
theorem large_non_normal_value_count : ∃ C : ℝ,0 < C ∧
    ∀ S x : ℝ,2 < S → 4 ≤ x → ∀ R Q : Finset ℕ,(∀ d ∈ R,0 < d) →
    (∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧ 4 ≤ p ∧
      x^(1/4:ℝ) ≤ p ∧ (v:ℝ) ≤ x ∧ ¬IsNormalPrime S p ∧ (n/p).totient ∈ R) →
    (Q.card:ℝ) ≤ (C*x/Real.log x*(B (2*x))^5*(Real.log S)^(-1/6:ℝ))*
      ∑ d ∈ R,(d:ℝ)⁻¹ := by
  classical
  obtain ⟨C,hC,hcount⟩ := non_normal_quarter_prime_count
  refine ⟨2*C,by positivity,?_⟩
  intro S x hS hx R Q hR hQ
  have hsub : Q ⊆ R.biUnion (abnormalExtensionValues S x) := by
    intro v hv
    obtain ⟨n,p,hn,hφ,hp,hpn,hp4,hpx,hvx,hbad,hr⟩ := hQ v hv
    refine Finset.mem_biUnion.mpr ⟨(n/p).totient,hr,?_⟩
    rw [← hφ]
    exact totient_mem_abnormalExtensionValues hn hp hpn hp4 hpx (by rwa [hφ]) hbad
  have hbound (d : ℕ) (hd : d ∈ R) :
      ((abnormalExtensionValues S x d).card:ℝ) ≤
      (2*C*x/Real.log x*(B (2*x))^5*(Real.log S)^(-1/6:ℝ))*(d:ℝ)⁻¹ := by
    have hh := hcount S x hS hx d (hR d hd) (abnormalExtensionPrimes S x d) (by
      intro p hp
      obtain ⟨hp,hp4,hbad⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp,hpx,hsize⟩ := (mem_quarterPrimes (hR d hd)).mp hp
      exact ⟨hp,hp4,hpx,hsize,hbad⟩)
    have hc : ((abnormalExtensionValues S x d).card:ℝ) ≤
        2*((abnormalExtensionPrimes S x d).card:ℝ) := by
      exact_mod_cast abnormal_extension_values_card S x d
    calc
      _ ≤ 2*((abnormalExtensionPrimes S x d).card:ℝ) := hc
      _ ≤ 2*(C*x/(d*Real.log x)*(B (2*x))^5*(Real.log S)^(-1/6:ℝ)) :=
        mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ ((R.biUnion (abnormalExtensionValues S x)).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ d ∈ R,((abnormalExtensionValues S x d).card:ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le : (R.biUnion (abnormalExtensionValues S x)).card ≤
        ∑ d ∈ R,(abnormalExtensionValues S x d).card)
    _ ≤ ∑ d ∈ R,(2*C*x/Real.log x*(B (2*x))^5*(Real.log S)^(-1/6:ℝ))*(d:ℝ)⁻¹ :=
      Finset.sum_le_sum hbound
    _ = _ := (Finset.mul_sum ..).symm

end TotientAsymptotic

end

end OAI
