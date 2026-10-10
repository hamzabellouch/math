import Mathlib
import OAI.Computability.QuantumFactoring.Basic
import OAI.Computability.QuantumFactoring.AuxiliaryTree

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

/-- Zero padding follows every positive entry. -/
def PaddedOrder (a b : ℕ) : Prop := b=0 ∨ (a≠0 ∧ a≤b)

def unpadProduct (xs : List ℕ) : ℕ := (xs.map (fun a => if a=0 then 1 else a)).prod

def FactorListValid (N : ℕ) (xs : List ℕ) : Prop :=
  (∀ a ∈ xs, a=0 ∨ a.Prime) ∧ xs.Pairwise PaddedOrder ∧ unpadProduct xs=N

lemma paddedOrder_append (ps : List ℕ) (k : ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hs : ps.Pairwise (·≤·)) : (ps++List.replicate k 0).Pairwise PaddedOrder := by
  rw [List.pairwise_append]
  refine ⟨hs.imp_of_mem ?_,?_,?_⟩
  · intro a b ha _hab hab
    exact Or.inr ⟨(hp a ha).ne_zero,hab⟩
  · apply List.pairwise_replicate.mpr
    exact Or.inr (Or.inl rfl)
  · intro a _ b hb
    have hb0 : b=0 := by simpa using (List.mem_replicate.mp hb).2
    exact Or.inl hb0

lemma unpadProduct_append (ps : List ℕ) (k : ℕ) (hp : ∀ p ∈ ps, p≠0) :
    unpadProduct (ps++List.replicate k 0)=ps.prod := by
  unfold unpadProduct
  rw [List.map_append,List.prod_append,List.map_replicate]
  simp only [ite_true,List.prod_replicate,one_pow,mul_one]
  congr 1
  conv_rhs => rw [← List.map_id ps]
  exact List.map_congr_left (fun p hp' => ite_eq_right (hp p hp'))

lemma FactorListValid.decompose {N : ℕ} {xs : List ℕ} (h : FactorListValid N xs) :
    ∃ ps : List ℕ, (∀ p ∈ ps, p.Prime) ∧ ps.Pairwise (·≤·) ∧ ps.prod=N ∧
      ps.length≤xs.length ∧ xs=ps++List.replicate (xs.length-ps.length) 0 := by
  rcases h with ⟨hp,hs,hprod⟩
  induction xs generalizing N with
  | nil => exact ⟨[],by simp,by simp,by simpa [unpadProduct] using hprod,by simp,by simp⟩
  | cons a xs ih =>
    have hpa : a=0 ∨ a.Prime := hp a (by simp)
    have hps : ∀ p ∈ xs, p=0 ∨ p.Prime := fun p h => hp p (by simp [h])
    have hsw := List.pairwise_cons.mp hs
    rcases hpa with rfl | ha
    · have hz : ∀ b ∈ xs, b=0 := by
        intro b hb
        rcases hsw.1 b hb with h | h
        · exact h
        · exact (h.1 rfl).elim
      have he : xs=List.replicate xs.length 0 := List.eq_replicate_of_mem hz
      have hn : N=1 := by
        rw [he] at hprod
        simpa [unpadProduct] using hprod.symm
      refine ⟨[],by simp,by simp,by simpa using hn.symm,by simp,?_⟩
      simp only [List.length_cons,List.length_nil,Nat.sub_zero,List.nil_append]
      rw [List.replicate_succ,← he]
    · obtain ⟨ps,hpp,hpsort,hpprod,hplen,hxeq⟩ :=
        ih hps hsw.2 (rfl : unpadProduct xs=unpadProduct xs)
      refine ⟨a::ps,?_,?_,?_,by simpa using hplen,?_⟩
      · intro p hp'
        rcases List.mem_cons.mp hp' with rfl | hp'
        · exact ha
        · exact hpp p hp'
      · rw [List.pairwise_cons]
        refine ⟨?_,hpsort⟩
        intro p hpm
        have hpx : p ∈ xs := by rw [hxeq]; exact List.mem_append_left _ hpm
        rcases hsw.1 p hpx with he | he
        · exact ((hpp p hpm).ne_zero he).elim
        · exact he.2
      · simp only [List.prod_cons,hpprod]
        simpa only [unpadProduct,List.map_cons,List.prod_cons,ite_eq_right ha.ne_zero] using hprod
      · simpa only [List.length_cons,Nat.add_sub_add_right,List.cons_append] using congrArg (List.cons a) hxeq

lemma factorListValid_iff {N n : ℕ} {xs : List ℕ} (hlen : xs.length=n) :
    FactorListValid N xs ↔ CorrectEncoding N n xs := by
  constructor
  · intro h
    simpa only [hlen,CorrectEncoding] using h.decompose
  · rintro ⟨ps,hp,hs,hprod,hplen,rfl⟩
    refine ⟨?_,paddedOrder_append ps _ hp hs,?_⟩
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact Or.inr (hp a ha)
      · exact Or.inl (List.mem_replicate.mp ha).2
    · exact (unpadProduct_append ps _ (fun p hp' => (hp p hp').ne_zero)).trans hprod

lemma correctEncoding_unique {N n : ℕ} {xs ys : List ℕ}
    (hx : CorrectEncoding N n xs) (hy : CorrectEncoding N n ys) : xs=ys := by
  obtain ⟨ps,hp,hs,hprod,_,rfl⟩ := hx
  obtain ⟨qs,hq,ht,hqprod,_,rfl⟩ := hy
  have hperm := (Nat.primeFactorsList_unique hprod hp).trans
    (Nat.primeFactorsList_unique hqprod hq).symm
  have he : ps=qs := hperm.eq_of_pairwise' hs ht
  rw [he]

/-- The valid sorted padded encoding exists and is unique, with every entry in
its n-bit range; the mathematical factor list here is used for analysis only. -/
theorem correctEncoding_exists {N n : ℕ} (hN : 2≤N) (hb : N<2^n) :
    ∃ xs : List ℕ, CorrectEncoding N n xs ∧ xs.length=n ∧ ∀ a ∈ xs, a<2^n := by
  have hn : N.primeFactorsList.length<n := AuxiliaryTree.splitWeight_bound (by omega) hb
  let xs := N.primeFactorsList++List.replicate (n-N.primeFactorsList.length) 0
  refine ⟨xs,⟨N.primeFactorsList,(fun p hp => Nat.prime_of_mem_primeFactorsList hp),
    (Nat.primeFactorsList_sorted N).pairwise,Nat.prod_primeFactorsList (by omega),hn.le,rfl⟩,?_,?_⟩
  · simp only [xs,List.length_append,List.length_replicate]
    omega
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (Nat.le_of_mem_primeFactorsList ha).trans_lt hb
    · have he := (List.mem_replicate.mp ha).2
      rw [he]
      positivity

end ExactQuantumFactoring


end

end OAI
