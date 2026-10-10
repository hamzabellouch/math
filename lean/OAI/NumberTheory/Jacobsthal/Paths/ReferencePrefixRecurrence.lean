import OAI.NumberTheory.Jacobsthal.Estimates.ReferenceProductsBasics

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferencePrefixRecurrence

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry ReferenceAdmission ReferencePruning
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def nonemptyPrefixes (P : Finset ℕ) : Finset (List ℕ) :=
  (decreasingPrefixes P).filter (fun ps => ps ≠ [])

theorem singleton_prefix_mem {P : Finset ℕ} {p : ℕ} (hp : p ∈ P) : [p] ∈ decreasingPrefixes P := by
  apply mem_decreasingPrefixes.mpr
  exact ⟨by simp,by intro q hq; simpa using List.mem_singleton.mp hq ▸ hp⟩

theorem nonempty_eq_first_completions (P : Finset ℕ) :
    nonemptyPrefixes P=P.biUnion (fun p => completions P [p]) := by
  ext ps
  constructor
  · intro hp
    obtain ⟨hpD,hne⟩ := Finset.mem_filter.mp hp
    cases ps with
    | nil => exact False.elim (hne rfl)
    | cons p ps =>
      have hpP : p ∈ P := (mem_decreasingPrefixes.mp hpD).2 p (by simp)
      have ht := (append_mem_decreasing_iff (singleton_prefix_mem hpP)).mp hpD
      exact Finset.mem_biUnion.mpr ⟨p,hpP,Finset.mem_image.mpr ⟨ps,ht,rfl⟩⟩
  · intro hp
    obtain ⟨p,hpP,hps⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨tail,htail,rfl⟩ := Finset.mem_image.mp hps
    exact Finset.mem_filter.mpr ⟨(append_mem_decreasing_iff (singleton_prefix_mem hpP)).mpr htail,by simp⟩

theorem first_completions_disjoint (P : Finset ℕ) :
    (P:Set ℕ).PairwiseDisjoint (fun p => completions P [p]) := by
  intro p _hp q _hq hne
  apply Finset.disjoint_left.mpr
  intro ps hp hq
  obtain ⟨sp,_hsp,he⟩ := Finset.mem_image.mp hp
  obtain ⟨sq,_hsq,hf⟩ := Finset.mem_image.mp hq
  have hh := he.trans hf.symm
  simp only [List.singleton_append] at hh
  exact hne (List.cons.inj hh).1

theorem sum_decreasing_by_first (P : Finset ℕ) (F : List ℕ → ℝ) :
    (∑ ps ∈ decreasingPrefixes P,F ps)=F []+
      ∑ p ∈ P,∑ ps ∈ decreasingPrefixes (P.filter (fun q => q<p)),F (p::ps) := by
  have he : (decreasingPrefixes P).filter (fun ps => ps=[])= {[]} := by
    ext ps
    simp only [Finset.mem_filter,Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · intro h
      subst ps
      exact ⟨mem_decreasingPrefixes.mpr ⟨by simp,by simp⟩,rfl⟩
  have hs := Finset.sum_filter_add_sum_filter_not (decreasingPrefixes P) (fun ps => ps=[]) F
  rw [he,Finset.sum_singleton] at hs
  change F []+(∑ ps ∈ nonemptyPrefixes P,F ps)=(∑ ps ∈ decreasingPrefixes P,F ps) at hs
  rw [← hs,nonempty_eq_first_completions,Finset.sum_biUnion (first_completions_disjoint P)]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  unfold completions
  rw [Finset.sum_image]
  · have hsuf : suffixPrimes P [p]=P.filter (fun q => q<p) := by simp [suffixPrimes]
    rw [hsuf]
    apply Finset.sum_congr rfl
    intro ps _
    rfl
  · intro a _ b _ h
    exact List.append_cancel_left h

theorem reference_polynomial_recurrence (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) :
    referencePolynomial w P i r=1-
      ∑ p ∈ P,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*referencePolynomial w (P.filter (fun q => q<p)) i.flip (r-primeExponent w p) else 0 := by
  have h := sum_decreasing_by_first P (fun ps => if admitted w i r ps then signedWeight ps else 0)
  have he : referencePolynomial w P i r =
      ∑ ps ∈ decreasingPrefixes P,if admitted w i r ps then signedWeight ps else 0 := by
    rw [referencePolynomial,referencePrefixes,Finset.sum_filter]
    rfl
  have hnil : (if admitted w i r [] then signedWeight [] else 0)=1 := by
    simp [admitted,signedWeight,prefixWeight]
  rw [he,h,hnil]
  have hsum : (∑ p ∈ P,∑ ps ∈ decreasingPrefixes (P.filter (fun q => q<p)),
      if admitted w i r (p::ps) then signedWeight (p::ps) else 0) =
      -(∑ p ∈ P,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*referencePolynomial w (P.filter (fun q => q<p)) i.flip (r-primeExponent w p) else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    by_cases hc : childAdmitted i r (primeExponent w p)
    · rw [ite_eq_left hc,referencePolynomial,referencePrefixes,Finset.sum_filter]
      rw [Finset.mul_sum,← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro ps _
      simp only [admitted,hc,true_and,signedWeight,List.length_cons,pow_succ,
        prefixWeight,List.map_cons,List.prod_cons]
      split_ifs <;> ring
    · simp [admitted,hc]
  rw [hsum]
  ring

end NumberTheoryLean.ReferencePrefixRecurrence

end

end Erdos970

end OAI
