import OAI.NumberTheory.TotientAsymptotic.PrimeExtensionCoverage
import OAI.NumberTheory.TotientAsymptotic.TupleTotients

namespace OAI

/-! Exact value counting by a selected prime divisor of a preimage. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def divisorExtensionValues (x : ℝ) (p : ℕ) : Finset ℕ :=
  (totientValues (x/(p-1:ℕ))).image (fun d => (p-1)*d) ∪
    (totientValues (x/(p-1:ℕ))).image (fun d => p*d)

lemma totient_mem_divisorExtensionValues {x : ℝ} {n p : ℕ}
    (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n) (hx : (n.totient:ℝ) ≤ x) :
    n.totient ∈ divisorExtensionValues x p := by
  classical
  have hq : 0 < n/p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
  have hd : 0 < (n/p).totient := Nat.totient_pos.mpr hq
  have hcases := totient_prime_extension_cases hp hpn
  have hsize : (((p-1)*(n/p).totient:ℕ):ℝ) ≤ x := by
    rcases hcases with h|h
    · rwa [← h]
    · exact (Nat.cast_le.mpr (Nat.mul_le_mul_right (n/p).totient (Nat.sub_le p 1))).trans (by rwa [← h])
  have hp1 : (0:ℝ) < (p-1:ℕ) := by exact_mod_cast (show 0 < p-1 by have := hp.two_le; omega)
  have hdsize : ((n/p).totient:ℝ) ≤ x/(p-1:ℕ) := by
    apply (le_div_iff₀ hp1).mpr
    simpa only [Nat.cast_mul,mul_comm] using hsize
  have hdmem : (n/p).totient ∈ totientValues (x/(p-1:ℕ)) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd,Nat.le_floor hdsize⟩,⟨n/p,hq,rfl⟩⟩
  rcases hcases with h|h
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(n/p).totient,hdmem,h.symm⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(n/p).totient,hdmem,h.symm⟩)

lemma divisorExtensionValues_card (x : ℝ) (p : ℕ) :
    ((divisorExtensionValues x p).card:ℝ) ≤ 2*V (x/(p-1:ℕ)) := by
  classical
  have hh : (divisorExtensionValues x p).card ≤
      (totientValues (x/(p-1:ℕ))).card+(totientValues (x/(p-1:ℕ))).card :=
    (Finset.card_union_le _ _).trans
      (Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le))
  change ((divisorExtensionValues x p).card:ℝ) ≤ 2*((totientValues (x/(p-1:ℕ))).card:ℝ)
  have hhR : ((divisorExtensionValues x p).card:ℝ) ≤
      ((totientValues (x/(p-1:ℕ))).card:ℝ)+(totientValues (x/(p-1:ℕ))).card := by
    exact_mod_cast hh
  linarith

theorem prime_divisor_value_count (x : ℝ) (P Q : Finset ℕ)
    (hQ : ∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
      (v:ℝ) ≤ x ∧ p ∈ P) :
    (Q.card:ℝ) ≤ 2*∑ p ∈ P,V (x/(p-1:ℕ)) := by
  classical
  have hs : Q ⊆ P.biUnion (divisorExtensionValues x) := by
    intro v hv
    obtain ⟨n,p,hn,hφ,hp,hpn,hvx,hP⟩ := hQ v hv
    refine Finset.mem_biUnion.mpr ⟨p,hP,?_⟩
    rw [← hφ]
    exact totient_mem_divisorExtensionValues hn hp hpn (by rwa [hφ])
  calc
    _ ≤ ((P.biUnion (divisorExtensionValues x)).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hs)
    _ ≤ ∑ p ∈ P,((divisorExtensionValues x p).card:ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le : (P.biUnion (divisorExtensionValues x)).card ≤
        ∑ p ∈ P,(divisorExtensionValues x p).card)
    _ ≤ ∑ p ∈ P,2*V (x/(p-1:ℕ)) := Finset.sum_le_sum (fun p _ => divisorExtensionValues_card x p)
    _ = _ := (Finset.mul_sum ..).symm

end TotientAsymptotic

end

end OAI
