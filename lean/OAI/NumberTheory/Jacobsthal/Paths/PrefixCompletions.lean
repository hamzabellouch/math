import OAI.NumberTheory.Jacobsthal.Estimates.FirstOmissionAntichain

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferencePruning
attribute [local instance] Classical.propDecidable
open ErdosPrimeInputs.PrimePrefixMass

noncomputable def suffixPrimes (P : Finset ℕ) (pre : List ℕ) : Finset ℕ :=
  P.filter (fun q => ∀ p ∈ pre,q < p)

theorem decreasing_prefix_mem {P : Finset ℕ} {pre suf : List ℕ}
    (h : pre++suf ∈ decreasingPrefixes P) : pre ∈ decreasingPrefixes P := by
  obtain ⟨hp,hm⟩ := mem_decreasingPrefixes.mp h
  exact mem_decreasingPrefixes.mpr ⟨(List.pairwise_append.mp hp).1,
    fun p hpre => hm p (List.mem_append.mpr (Or.inl hpre))⟩

theorem append_mem_decreasing_iff {P : Finset ℕ} {pre suf : List ℕ}
    (hpre : pre ∈ decreasingPrefixes P) :
    pre++suf ∈ decreasingPrefixes P ↔ suf ∈ decreasingPrefixes (suffixPrimes P pre) := by
  obtain ⟨hpp,hpm⟩ := mem_decreasingPrefixes.mp hpre
  constructor
  · intro h
    obtain ⟨hp,hm⟩ := mem_decreasingPrefixes.mp h
    obtain ⟨_,hs,hcross⟩ := List.pairwise_append.mp hp
    apply mem_decreasingPrefixes.mpr
    refine ⟨hs,?_⟩
    intro q hq
    apply Finset.mem_filter.mpr
    exact ⟨hm q (List.mem_append.mpr (Or.inr hq)),fun p hp => hcross p hp q hq⟩
  · intro h
    obtain ⟨hs,hm⟩ := mem_decreasingPrefixes.mp h
    apply mem_decreasingPrefixes.mpr
    refine ⟨List.pairwise_append.mpr ⟨hpp,hs,?_⟩,?_⟩
    · intro p hp q hq
      exact (Finset.mem_filter.mp (hm q hq)).2 p hp
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hpm p hp
      · exact (Finset.mem_filter.mp (hm p hp)).1

theorem suffixPrimes_append_singleton {P : Finset ℕ} {pre : List ℕ} {p : ℕ}
    (hp : pre++[p] ∈ decreasingPrefixes P) :
    suffixPrimes P (pre++[p]) = P.filter (fun q => q < p) := by
  have hcross := (List.pairwise_append.mp (mem_decreasingPrefixes.mp hp).1).2.2
  ext q
  simp only [suffixPrimes,Finset.mem_filter]
  constructor
  · rintro ⟨hq,hall⟩
    exact ⟨hq,hall p (by simp)⟩
  · rintro ⟨hq,hqp⟩
    refine ⟨hq,?_⟩
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hqp.trans (hcross a ha p (by simp))
    · have he : a = p := by simpa only [List.mem_singleton] using ha
      simpa only [he] using hqp

noncomputable def completions (P : Finset ℕ) (pre : List ℕ) : Finset (List ℕ) :=
  (decreasingPrefixes (suffixPrimes P pre)).image (fun suf => pre++suf)

end NumberTheoryLean.ReferencePruning

end

end Erdos970

end OAI
