import OAI.Combinatorics.SquareDifference.InductiveBounds

namespace OAI

section

open Finset

namespace SquareDifference

structure SourcePrimeHyp {S J : Type} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
    (ps : S → ℕ) (p : J → ℕ) [∀s,Fact (ps s).Prime] [∀j,Fact (p j).Prime] (N : ℕ) : Prop where
  injective : Function.Injective (extendedPrime ps p)
  lower : ∀j,64≤p j
  mass : ∀j,max tupleMassThreshold tupleConditionalThreshold≤(p j:ℝ)
  reflection : ∀j,tupleReflectionThreshold≤(p j:ℝ)
  coprime : ∀j,(smallModulus ps).Coprime (p j)
  exceptional : ∀j,tupleEta (p j)≤1/(p j:ℝ)^4
  cover : ∀r : ℕ,r.Prime → r≤N → ∃i,extendedPrime ps p i=r

lemma SourcePrimeHyp.mono {S J : Type} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
    {ps : S → ℕ} {p : J → ℕ} [∀s,Fact (ps s).Prime] [∀j,Fact (p j).Prime]
    {N n : ℕ} (h : SourcePrimeHyp ps p N) (hn : n≤N) : SourcePrimeHyp ps p n :=
  ⟨h.injective,h.lower,h.mass,h.reflection,h.coprime,h.exceptional,fun r hr hrn => h.cover r hr (hrn.trans hn)⟩

def smallPrimeSet (P : ℕ) : Finset ℕ := (range P).filter Nat.Prime

def largePrimeSet (P N : ℕ) : Finset ℕ := (Icc P N).filter Nat.Prime

abbrev SmallPrime (P : ℕ) := ↥(smallPrimeSet P)

abbrev LargePrime (P N : ℕ) := ↥(largePrimeSet P N)

def smallPrimes (P : ℕ) : SmallPrime P → ℕ := Subtype.val

def largePrimes (P N : ℕ) : LargePrime P N → ℕ := Subtype.val

instance smallPrimes_fact (P : ℕ) (s : SmallPrime P) : Fact (smallPrimes P s).Prime :=
  ⟨(mem_filter.mp s.property).2⟩

instance largePrimes_fact (P N : ℕ) (s : LargePrime P N) : Fact (largePrimes P N s).Prime :=
  ⟨(mem_filter.mp s.property).2⟩

lemma smallPrimes_lt (P : ℕ) (s : SmallPrime P) : smallPrimes P s<P := mem_range.mp (mem_filter.mp s.property).1

lemma largePrimes_ge (P N : ℕ) (s : LargePrime P N) : P≤largePrimes P N s := (mem_Icc.mp (mem_filter.mp s.property).1).1

lemma smallPrimes_injective (P : ℕ) : Function.Injective (smallPrimes P) := Subtype.val_injective

lemma actualPrime_injective (P N : ℕ) : Function.Injective (extendedPrime (smallPrimes P) (largePrimes P N)) := by
  intro i j hij
  cases i with
  | inl i => cases j with
    | inl j => exact congrArg Sum.inl (Subtype.ext hij)
    | inr j => have h1 := smallPrimes_lt P i; have h2 := largePrimes_ge P N j; change smallPrimes P i=largePrimes P N j at hij; omega
  | inr i => cases j with
    | inl j => have h1 := largePrimes_ge P N i; have h2 := smallPrimes_lt P j; change largePrimes P N i=smallPrimes P j at hij; omega
    | inr j => exact congrArg Sum.inr (Subtype.ext hij)

lemma actualPrime_cover (P N : ℕ) (r : ℕ) (hr : r.Prime) (hrN : r≤N) :
    ∃i,extendedPrime (smallPrimes P) (largePrimes P N) i=r := by
  by_cases h : r<P
  · exact ⟨Sum.inl ⟨r,mem_filter.mpr ⟨mem_range.mpr h,hr⟩⟩,rfl⟩
  · exact ⟨Sum.inr ⟨r,mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hrN⟩,hr⟩⟩,rfl⟩

lemma smallQuadraticModulus_coprime {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hne : q≠p) :
    (smallQuadraticModulus q).Coprime p := by
  have hc := (Nat.coprime_primes hq hp).mpr hne
  by_cases h2 : q=2
  · subst q
    simpa only [smallQuadraticModulus,ite_true,show 2^3=8 by norm_num] using hc.pow_left 3
  · simpa only [smallQuadraticModulus,h2,ite_false] using hc

lemma actualPrime_coprime (P N : ℕ) (j : LargePrime P N) :
    (smallModulus (smallPrimes P)).Coprime (largePrimes P N j) := by
  apply Nat.Coprime.prod_left
  intro s _
  apply smallQuadraticModulus_coprime (Fact.out : (smallPrimes P s).Prime) (Fact.out : (largePrimes P N j).Prime)
  have hs := smallPrimes_lt P s
  have hj := largePrimes_ge P N j
  omega

lemma actualSmallModulus_ge_two (P : ℕ) (hP : 3≤P) : 2 ≤ smallModulus (smallPrimes P) := by
  let s : SmallPrime P := ⟨2,mem_filter.mpr ⟨mem_range.mpr (by omega),Nat.prime_two⟩⟩
  have hd := smallModulus_dvd (smallPrimes P) s
  have he : smallQuadraticModulus (smallPrimes P s)=8 := by simp only [smallPrimes,s,smallQuadraticModulus,ite_true]
  rw [he] at hd
  have hh := Nat.le_of_dvd (smallModulus_pos (smallPrimes P)) hd
  omega

lemma actualPrime_hyp (P : ℕ) (hP : 64≤P)
    (ht : ∀{p : ℕ} [Fact p.Prime],P≤p → max tupleMassThreshold tupleConditionalThreshold≤(p:ℝ) ∧
      tupleReflectionThreshold≤(p:ℝ) ∧ tupleEta p≤1/(p:ℝ)^4) (N : ℕ) :
    SourcePrimeHyp (smallPrimes P) (largePrimes P N) N := by
  have hh (j : LargePrime P N) := ht (largePrimes_ge P N j)
  exact ⟨actualPrime_injective P N,fun j => hP.trans (largePrimes_ge P N j),fun j => (hh j).1,
    fun j => (hh j).2.1,actualPrime_coprime P N,fun j => (hh j).2.2,actualPrime_cover P N⟩

end SquareDifference

end

end OAI
