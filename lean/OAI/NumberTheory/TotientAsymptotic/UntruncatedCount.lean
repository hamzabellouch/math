import OAI.NumberTheory.TotientAsymptotic.UntruncatedRemainder
import OAI.NumberTheory.TotientAsymptotic.LargestPrimeCount

namespace OAI

noncomputable section
open scoped BigOperators Topology Classical
open Filter

namespace TotientAsymptotic

lemma untruncated_totient_lower {x : ℝ} {H p : ℕ} {η : RemainderDatum (L x H)}
    (hη : IsUntruncatedRemainder x H η) (hp : p.Prime) :
    (p-1)*(η.cofactor.totient*∏ i : Fin (L x H), (η.primes i-1)) ≤
      (wholePreimage p η).totient := by
  have hprime (i : Fin (L x H)) : (η.primes i).Prime := by
    have hh := (hη.2.1.2.1 (i.val+1) (Finset.mem_Icc.mpr
      ⟨by omega,by have := i.isLt; omega⟩)).1
    simpa [primeOnly,remainderPrime,i.isLt] using hh
  have htail := totient_prime_product_lower Finset.univ η.primes η.cofactor (fun i _ => hprime i)
  have he : suffixPreimage η 0=η.cofactor*∏ i, η.primes i := by
    unfold suffixPreimage
    rw [← prod_fin_shifted (L x H) (remainderPrime η)]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    simp [remainderPrime,i.isLt]
  rw [wholePreimage,he]
  calc
    _ ≤ (p-1)*(η.cofactor*∏ i, η.primes i).totient := Nat.mul_le_mul_left _ htail
    _ = p.totient*(η.cofactor*∏ i, η.primes i).totient := by rw [Nat.totient_prime hp]
    _ ≤ _ := Nat.totient_super_multiplicative _ _

/-- Count any finite family before truncating its smooth cofactor. The
largest-prime count is uniform in both the cofactor and the prime vector. -/
theorem untruncated_witness_count : ∀ᶠ x : ℝ in atTop, ∀ H : ℕ,
    ∀ S : Finset (RemainderDatum (L x H) × ℕ),
    (∀ q ∈ S, IsUntruncatedRemainder x H q.1 ∧ q.2.Prime ∧
      x^(9/10 : ℝ) ≤ q.2 ∧ ((wholePreimage q.2 q.1).totient : ℝ) ≤ x) →
    (S.card : ℝ) ≤ (10*x/Real.log x)*
      ∑ η ∈ S.image Prod.fst, (η.cofactor.totient : ℝ)⁻¹*reciprocalShiftWeight η.primes := by
  classical
  filter_upwards [largest_prime_count_upper] with x hx
  intro H S hS
  let E := S.image Prod.fst
  have he : (S.card : ℝ)=∑ η ∈ E, ((S.filter (fun q => q.1=η)).card : ℝ) := by
    rw [← Nat.cast_sum]
    congr 1
    rw [Finset.sum_card_fiberwise_eq_card_filter S E Prod.fst]
    congr 1
    exact (Finset.filter_eq_self.mpr (fun q hq => Finset.mem_image.mpr ⟨q,hq,rfl⟩)).symm
  rw [he,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro η hη
  obtain ⟨q,hq,hqη⟩ := Finset.mem_image.mp hη
  have hηb : IsUntruncatedRemainder x H η := hqη ▸ (hS q hq).1
  let D := η.cofactor.totient*∏ i, (η.primes i-1)
  have hD : 0 < D := by
    apply Nat.mul_pos (Nat.totient_pos.mpr hηb.1)
    apply Finset.prod_pos
    intro i _
    have hp := (hηb.2.1.2.1 (i.val+1) (Finset.mem_Icc.mpr
      ⟨by omega,by have := i.isLt; omega⟩)).1
    have hp' : (η.primes i).Prime := by simpa [primeOnly,remainderPrime,i.isLt] using hp
    exact Nat.sub_pos_of_lt hp'.one_lt
  let Q := (S.filter (fun q => q.1=η)).image Prod.snd
  have hcard : (S.filter (fun q => q.1=η)).card=Q.card := by
    symm
    apply Finset.card_image_of_injOn
    intro a ha b hb heq
    exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) heq
  rw [hcard]
  have hb := hx D hD Q (by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hq,heq⟩ := Finset.mem_filter.mp hq
    obtain ⟨hη',hp,hmin,hval⟩ := hS q hq
    refine ⟨hp,hmin,?_⟩
    have hlower := untruncated_totient_lower hη' hp
    rw [heq] at hlower
    have hh : (((q.2-1)*D : ℕ) : ℝ) ≤ (wholePreimage q.2 η).totient := by exact_mod_cast hlower
    exact hh.trans (by simpa only [heq] using hval))
  apply hb.trans_eq
  dsimp [D]
  simp only [reciprocalShiftWeight,Nat.cast_mul,Nat.cast_prod]
  field_simp

end TotientAsymptotic

end

end OAI
