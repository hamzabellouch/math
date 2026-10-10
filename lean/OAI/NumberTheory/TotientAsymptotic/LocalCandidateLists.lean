import OAI.NumberTheory.TotientAsymptotic.LocalNormalCandidates
import OAI.NumberTheory.TotientAsymptotic.CandidatePrimeList

namespace OAI

/-! The local normality requirements persist after every removed prefix. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma candidatePrimeAt_zero {n : ℕ} (p : Fin n → ℕ) (q : ℕ) :
    candidatePrimeAt p q 0=q := by
  simpa only [Fin.val_zero,Fin.cons_zero] using candidatePrimeAt_fin p q (0 : Fin (n+1))

lemma candidatePrimeAt_succ {n : ℕ} (p : Fin n → ℕ) (q i : ℕ) (hi : i<n) :
    candidatePrimeAt p q (i+1)=p ⟨i,hi⟩ := by
  simpa only [Fin.val_succ,Fin.cons_succ] using
    candidatePrimeAt_fin p q (Fin.succ ⟨i,hi⟩)

lemma candidatePrimeAt_local_normality {m n : ℕ} (p : Fin n → ℕ) (q : ℕ)
    (hq : IsNormalPrime (localNormalityScale m) q)
    (hp : ∀ i j : Fin n,i ≤ j → IsNormalPrime (localNormalityScale (m-i.val)) (p j)) :
    ∀ J k : ℕ,J ≤ k → k < n+1 →
      IsNormalPrime (localNormalityScale (m-(J-1))) (candidatePrimeAt p q k) := by
  intro J k hJk hk
  by_cases hk0 : k=0
  · have hJ0 : J=0 := by omega
    simpa only [hk0,hJ0,Nat.zero_sub,Nat.sub_zero,candidatePrimeAt_zero] using hq
  have hk' : k-1<n := by omega
  have hkE : k-1+1=k := by omega
  rw [←hkE,candidatePrimeAt_succ p q (k-1) hk']
  have hJ : J-1<n := by omega
  exact hp ⟨J-1,hJ⟩ ⟨k-1,hk'⟩ (by change J-1 ≤ k-1; omega)

theorem local_normal_candidate_list_data {c : ℝ} (hc : 0 < c)
    (d : ℕ) (hd : 0 < d) (L : ℕ) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∃ p : ℕ → ℕ → ℕ,∀ b ∈ localNormalCandidates x c d L H,
        b=pptSuffixProduct (p b) (m x-H+1) 0 ∧
        (∀ i < m x-H+1,(p b i).Prime) ∧
        (∀ i k : ℕ,i < k → k < m x-H+1 → p b k < p b i) ∧
        (∀ i < m x-H+1,d+1 < p b i) ∧
        ∀ J k : ℕ,J ≤ k → k < m x-H+1 →
          IsNormalPrime (localNormalityScale (m x-(J-1))) (p b k) := by
  classical
  filter_upwards [head_limited_prime_coordinates hc,raw_candidate_rough hc d hd] with H hcoord hrough
  filter_upwards [hcoord,hrough,m_tendsto.eventually (eventually_ge_atTop H),
    capped_prime_tail_denominator hd,head_interval_above_tail]
    with x hcoord hrough hm hdenom hhead
  have hex (b : ℕ) (hb : b ∈ localNormalCandidates x c d L H) :
      ∃ r : ℕ → ℕ,b=pptSuffixProduct r (m x-H+1) 0 ∧
        (∀ i < m x-H+1,(r i).Prime) ∧
        (∀ i k : ℕ,i < k → k < m x-H+1 → r k < r i) ∧
        (∀ i < m x-H+1,d+1 < r i) ∧
        ∀ J k : ℕ,J ≤ k → k < m x-H+1 →
          IsNormalPrime (localNormalityScale (m x-(J-1))) (r k) := by
    obtain ⟨p,q,he,hpQ,hinterval,hqnormal,hpnorm⟩ := local_normal_candidate_representation hb
    obtain ⟨hpr,hr,hcap⟩ := hcoord _ (Nat.sub_add_cancel hm) p (local_regular_tuples_subset hpQ)
    have ho := prime_coordinates_strictAnti hpr hr.1.2.1
    have hD : (1:ℝ) ≤ ((d*(∏ i,p i).totient:ℕ):ℝ) := by
      exact_mod_cast Nat.mul_pos hd (Nat.totient_pos.mpr
        (Finset.prod_pos (fun i _ => (hpr i).pos)))
    obtain ⟨hq,hqp⟩ := hhead _ hD (hdenom _ (Nat.sub_le _ _) p hpr hcap) _ p hpr hcap q hinterval
    let r := candidatePrimeAt p q
    have hprod := candidatePrimeAt_product p q
    have hrpr := candidatePrimeAt_prime p hpr hq
    refine ⟨r,he.trans hprod.symm,hrpr,candidatePrimeAt_order p ho hqp,?_,
      candidatePrimeAt_local_normality p q hqnormal hpnorm⟩
    intro i hi
    apply hrough b (local_regular_candidates_subset (local_normal_candidates_subset hb))
      (r i) (hrpr i hi)
    rw [he,←hprod]
    exact Finset.dvd_prod_of_mem r (Finset.mem_Ico.mpr ⟨Nat.zero_le _,hi⟩)
  choose p hp using hex
  refine ⟨fun b => if hb : b ∈ localNormalCandidates x c d L H then p b hb else fun _ => 1,?_⟩
  intro b hb
  simpa only [dite_eq_left hb] using hp b hb

end TotientAsymptotic

end

end OAI
