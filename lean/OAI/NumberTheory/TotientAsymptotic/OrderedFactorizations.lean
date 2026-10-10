import OAI.NumberTheory.TotientAsymptotic.SquarefreeCollisionMass
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace OAI

/-! Concrete finite encodings for ordered multiplicative factorizations. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def multiplyFactor {k : ℕ} (i : Fin k) (p : ℕ) (f : Fin k → ℕ) : Fin k → ℕ :=
  Function.update f i (p*f i)

lemma prod_multiplyFactor {k : ℕ} (i : Fin k) (p : ℕ) (f : Fin k → ℕ) :
    (∏ j,multiplyFactor i p f j)=p*(∏ j,f j) := by
  have he := Finset.prod_update_of_mem (Finset.mem_univ i) f (f i)
  simp only [Function.update_eq_self] at he
  rw [multiplyFactor,Finset.prod_update_of_mem (Finset.mem_univ i),he]
  ring

def factorAllocations (k : ℕ) : List ℕ → Finset (Fin k → ℕ)
  | [] => {fun _ => 1}
  | p::L => ((Finset.univ : Finset (Fin k)) ×ˢ factorAllocations k L).image
      (fun t => multiplyFactor t.1 p t.2)

lemma factorAllocations_card_le (k : ℕ) (L : List ℕ) :
    (factorAllocations k L).card ≤ k^L.length := by
  induction L with
  | nil => simp [factorAllocations]
  | cons p L ih =>
    calc
      _ ≤ ((Finset.univ : Finset (Fin k)) ×ˢ factorAllocations k L).card := Finset.card_image_le
      _ = k*(factorAllocations k L).card := by rw [Finset.card_product]; simp
      _ ≤ k*k^L.length := Nat.mul_le_mul_left k ih
      _ = _ := by simp [pow_succ,mul_comm]

lemma mem_factorAllocations {k : ℕ} (L : List ℕ)
    (hL : ∀ p ∈ L,p.Prime) (f : Fin k → ℕ) (hf : (∏ j,f j)=L.prod) :
    f ∈ factorAllocations k L := by
  induction L generalizing f with
  | nil =>
    have he : f=fun _ => 1 := by
      funext j
      apply Nat.eq_one_of_dvd_one
      simpa only [hf,List.prod_nil] using Finset.dvd_prod_of_mem f (Finset.mem_univ j)
    simp [factorAllocations,he]
  | cons p L ih =>
    have hp := hL p (List.mem_cons_self ..)
    have hd : p ∣ ∏ j,f j := by rw [hf,List.prod_cons]; exact dvd_mul_right p L.prod
    obtain ⟨i,_,hi⟩ := (hp.prime.dvd_finsetProd_iff f).mp hd
    let g := Function.update f i (f i/p)
    have he : multiplyFactor i p g=f := by
      funext j
      by_cases hj : j=i
      · subst j
        simp [multiplyFactor,g,Nat.mul_div_cancel' hi]
      · simp [multiplyFactor,g,hj]
    have hg : (∏ j,g j)=L.prod := by
      apply Nat.eq_of_mul_eq_mul_left hp.pos
      rw [← prod_multiplyFactor i p g,he,hf,List.prod_cons]
    apply Finset.mem_image.mpr
    exact ⟨(i,g),Finset.mem_product.mpr ⟨Finset.mem_univ _,
      ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)) g hg⟩,he⟩

/-- Independent left and right allocations give the collision multiplicity. -/
theorem paired_factorizations_card_le (k n : ℕ) (hn : 0 < n)
    (Q : Finset ((Fin k → ℕ) × (Fin k → ℕ)))
    (hQ : ∀ f ∈ Q,(∏ j,f.1 j)=n ∧ (∏ j,f.2 j)=n) :
    Q.card ≤ k^(2*n.primeFactorsList.length) := by
  let A := factorAllocations k n.primeFactorsList
  have hsub : Q ⊆ A ×ˢ A := by
    intro f hf
    obtain ⟨hl,hr⟩ := hQ f hf
    apply Finset.mem_product.mpr
    constructor
    · apply mem_factorAllocations n.primeFactorsList (fun p hp => Nat.prime_of_mem_primeFactorsList hp)
      simpa only [Nat.prod_primeFactorsList hn.ne'] using hl
    · apply mem_factorAllocations n.primeFactorsList (fun p hp => Nat.prime_of_mem_primeFactorsList hp)
      simpa only [Nat.prod_primeFactorsList hn.ne'] using hr
  calc
    Q.card ≤ (A ×ˢ A).card := Finset.card_le_card hsub
    _ = A.card*A.card := Finset.card_product A A
    _ ≤ k^n.primeFactorsList.length*k^n.primeFactorsList.length :=
      Nat.mul_le_mul (factorAllocations_card_le k _) (factorAllocations_card_le k _)
    _ = _ := by rw [two_mul,pow_add]

end TotientAsymptotic

end

end OAI
