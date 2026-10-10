import OAI.NumberTheory.TotientAsymptotic.CandidateRoughness
import OAI.NumberTheory.TotientAsymptotic.PPTMaximalSuffix

namespace OAI

/-! The counted prime tuples as finite ordered lists for prefix cancellation. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

def candidatePrimeAt {n : ℕ} (p : Fin n → ℕ) (q i : ℕ) : ℕ :=
  if hi : i < n+1 then (Fin.cons q p : Fin (n+1) → ℕ) ⟨i,hi⟩ else 1

lemma candidatePrimeAt_fin {n : ℕ} (p : Fin n → ℕ) (q : ℕ) (i : Fin (n+1)) :
    candidatePrimeAt p q i= (Fin.cons q p : Fin (n+1) → ℕ) i := by
  simp only [candidatePrimeAt,dite_eq_left i.isLt]

lemma candidatePrimeAt_product {n : ℕ} (p : Fin n → ℕ) (q : ℕ) :
    pptSuffixProduct (candidatePrimeAt p q) (n+1) 0=q*(∏ i,p i) := by
  unfold pptSuffixProduct
  rw [Nat.Ico_zero_eq_range,Finset.prod_range]
  simp only [candidatePrimeAt_fin,Fin.prod_cons]

lemma candidatePrimeAt_prime {n : ℕ} (p : Fin n → ℕ) {q : ℕ}
    (hp : ∀ i,(p i).Prime) (hq : q.Prime) :
    ∀ i < n+1,(candidatePrimeAt p q i).Prime := by
  intro i hi
  have hh : ∀ j : Fin (n+1),((Fin.cons q p : Fin (n+1) → ℕ) j).Prime := by
    intro j
    refine Fin.cases hq (fun k => hp k) j
  simpa only [candidatePrimeAt,dite_eq_left hi] using hh ⟨i,hi⟩

lemma candidatePrimeAt_order {n : ℕ} (p : Fin n → ℕ) {q : ℕ}
    (hp : StrictAnti p) (hq : ∀ i,p i < q) :
    ∀ i k : ℕ,i < k → k < n+1 → candidatePrimeAt p q k < candidatePrimeAt p q i := by
  have ho : StrictAnti (Fin.cons q p) := by
    apply (Fin.strictMono_cons (α:=OrderDual ℕ)).mpr
    exact ⟨hq,hp⟩
  intro i k hik hk
  have hi : i < n+1 := hik.trans hk
  simpa only [candidatePrimeAt,dite_eq_left hi,dite_eq_left hk] using
    ho (show (⟨i,hi⟩:Fin (n+1)) < ⟨k,hk⟩ from hik)

theorem raw_candidate_list_data {c : ℝ} (hc : 0 < c) (d : ℕ) (hd : 0 < d) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∃ p : ℕ → ℕ → ℕ,∀ b ∈ rawCandidates x c d H,
        b=pptSuffixProduct (p b) (m x-H+1) 0 ∧
        (∀ i < m x-H+1,(p b i).Prime) ∧
        (∀ i k : ℕ,i < k → k < m x-H+1 → p b k < p b i) ∧
        ∀ i < m x-H+1,d+1 < p b i := by
  classical
  filter_upwards [raw_candidate_prime_data hc d hd,raw_candidate_rough hc d hd]
    with H hH hrough
  filter_upwards [hH,hrough] with x hx hr
  have hex (b : ℕ) (hb : b ∈ rawCandidates x c d H) :
      ∃ p : ℕ → ℕ,b=pptSuffixProduct p (m x-H+1) 0 ∧
        (∀ i < m x-H+1,(p i).Prime) ∧
        (∀ i k : ℕ,i < k → k < m x-H+1 → p k < p i) ∧
        ∀ i < m x-H+1,d+1 < p i := by
    obtain ⟨p,q,rfl,hp,ho,_,_,_,hq,hqp,_⟩ := hx b hb
    let r := candidatePrimeAt p q
    have he := candidatePrimeAt_product p q
    have hp' := candidatePrimeAt_prime p hp hq
    refine ⟨r,he.symm,hp',candidatePrimeAt_order p ho hqp,?_⟩
    intro i hi
    apply hr _ hb _ (hp' i hi)
    rw [←he]
    exact Finset.dvd_prod_of_mem r (Finset.mem_Ico.mpr ⟨Nat.zero_le _,hi⟩)
  choose p hp using hex
  refine ⟨fun b => if hb : b ∈ rawCandidates x c d H then p b hb else fun _ => 1,?_⟩
  intro b hb
  simpa only [dite_eq_left hb] using hp b hb

end TotientAsymptotic

end

end OAI
