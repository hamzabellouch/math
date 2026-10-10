import OAI.NumberTheory.TotientAsymptotic.TailHeadCount

namespace OAI

/-! The head-prime extension counts actual distinct integers and their totients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def candidateIntegers {n : ℕ} (x : ℝ) (d : ℕ) (Q : Finset (Fin n → ℕ)) : Finset ℕ :=
  (tailHeadPairs x d Q).image (fun z => z.2*(∏ i,z.1 i))

lemma candidateIntegers_card {n : ℕ} {x : ℝ} {d : ℕ} {Q : Finset (Fin n → ℕ)}
    (hQ : ∀ p ∈ Q,(∀ i,(p i).Prime) ∧ StrictAnti p)
    (hhead : ∀ z ∈ tailHeadPairs x d Q,z.2.Prime ∧ ∀ i,z.1 i < z.2) :
    (candidateIntegers x d Q).card=(tailHeadPairs x d Q).card := by
  apply Finset.card_image_of_injOn
  intro z hz w hw he
  obtain ⟨hzQ,_⟩ := Finset.mem_sigma.mp hz
  obtain ⟨hwQ,_⟩ := Finset.mem_sigma.mp hw
  obtain ⟨hp,hpo⟩ := hQ z.1 hzQ
  obtain ⟨hq,hqo⟩ := hQ w.1 hwQ
  obtain ⟨hza,hzg⟩ := hhead z hz
  obtain ⟨hwa,hwg⟩ := hhead w hw
  obtain ⟨heh,het⟩ := ordered_head_product_injective hp hq hza hwa hpo hqo hzg hwg he
  exact Sigma.ext het (heq_of_eq heh)

lemma candidate_prime_extension_totient {n : ℕ} {p : Fin n → ℕ} {q : ℕ}
    (hp : ∀ i,(p i).Prime) (hq : q.Prime) (hqp : ∀ i,p i < q) :
    (q*(∏ i,p i)).totient=(q-1)*(∏ i,p i).totient := by
  have hcop : q.Coprime (∏ i,p i) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro i _
    apply hq.coprime_iff_not_dvd.mpr
    intro hdvd
    have hh := Nat.le_of_dvd (hp i).pos hdvd
    exact (not_le_of_gt (hqp i)) hh
  rw [Nat.totient_mul hcop,Nat.totient_prime hq]

lemma candidate_totient_bound {n : ℕ} {x : ℝ} (hx : 0 ≤ x) {d : ℕ} (hd : 0 < d)
    {p : Fin n → ℕ} {q : ℕ} (hp : ∀ i,(p i).Prime)
    (hq : q ∈ primeInterval (x/(2*((d*(∏ i,p i).totient:ℕ):ℝ)))
      (x/((d*(∏ i,p i).totient:ℕ):ℝ))) (hqp : ∀ i,p i < q) :
    ((d*(q*(∏ i,p i)).totient:ℕ):ℝ) ≤ x := by
  have hr : 0 < ∏ i,p i := Finset.prod_pos (fun i _ => (hp i).pos)
  have hD : (0:ℝ) < ((d*(∏ i,p i).totient:ℕ):ℝ) := by
    exact_mod_cast Nat.mul_pos hd (Nat.totient_pos.mpr hr)
  obtain ⟨hqprime,_,hqu⟩ := mem_head_prime_interval hx hD hq
  rw [candidate_prime_extension_totient hp hqprime hqp]
  have hh := (le_div_iff₀ hD).mp hqu
  have hle : (q-1:ℝ)*((d*(∏ i,p i).totient:ℕ):ℝ) ≤ x := by
    nlinarith only [hh,hD]
  push_cast
  rw [Nat.cast_sub hqprime.one_le,Nat.cast_one]
  push_cast at hle
  nlinarith only [hle]

end TotientAsymptotic

end

end OAI
