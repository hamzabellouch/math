import OAI.NumberTheory.CubicMoment.Estimates.SelectedPrimeGeometry

namespace OAI

/-! The original selected-divisor sum is exactly the finite collection
of free-prime rows. Its squarefree support, global largest-prime choice,
output interval, exclusion and stopping predicates are all retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def selectedStoppedDivisorSet (B ρ a b : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (r e : Eisenstein) : Finset Eisenstein :=
  (primaryElementBall B).filter (fun d =>
    Squarefree (r*d) ∧ (primaryPrimeFactors d).Nonempty ∧ IsCoprime (r*d) e ∧
      (a < norm (r*d) ∧ norm (r*d) ≤ b) ∧ largestPrimeChoice (r*d) ∣ d ∧
      geometricPrimeBin ρ B (largestPrimeChoice (r*d)) = j ∧
      stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B) j₀ k h Z Q early r d)

def selectedStoppedRowPairs (B ρ a b : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (r e : Eisenstein) : Finset (Eisenstein × Eisenstein) :=
  ((primaryElementBall B) ×ˢ (primeCutoff B)).filter (fun t =>
    Squarefree (r*t.1) ∧ IsCoprime (r*t.1) e ∧
      t.2 ∈ stoppedSelectedPrimeSet B ρ (a/norm (r*t.1)) (b/norm (r*t.1))
        j j₀ k h Z Q early r t.1 e)

lemma selectedStopped_forward (B ρ a b : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    {r e d : Eisenstein} (hr : primary r)
    (hd : d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e) :
    (largestPrimeRemainder d,largestPrimeChoice d) ∈
      selectedStoppedRowPairs B ρ a b j j₀ k h Z Q early r e := by
  obtain ⟨hd,hs,hne,hcop,hint,hrole,hbin,hstop⟩ := Finset.mem_filter.mp hd
  obtain ⟨hd,hdB⟩ := mem_primaryElementBall.mp hd
  obtain ⟨hp,hc,hsc,hpc,he,hl⟩ := largestPrimeChoice_decomposition hd
    (squarefree_mul_iff.mp hs).2.2 hne
  have hfull : largestPrimeChoice (r*d) = largestPrimeChoice d :=
    (largestPrimeChoice_dvd_right_iff hr hd hne).mp hrole
  have hpB : norm (largestPrimeChoice d) ≤ B :=
    (norm_le_of_dvd_nonzero (primary_ne_zero hd) ⟨largestPrimeRemainder d,he.symm⟩).trans hdB
  have hcB : norm (largestPrimeRemainder d) ≤ B :=
    (norm_le_of_dvd_nonzero (primary_ne_zero hd)
      ⟨largestPrimeChoice d,by rw [mul_comm,he]⟩).trans hdB
  have hs' : Squarefree (r*(largestPrimeChoice d*largestPrimeRemainder d)) := by rw [he]; exact hs
  have hcop' : IsCoprime (r*(largestPrimeChoice d*largestPrimeRemainder d)) e := by
    rw [he]; exact hcop
  obtain ⟨hsrc,hrce,hpcre⟩ := (selectedPrime_product_conditions r _ _ e hp).mp ⟨hs',hcop'⟩
  have hlarge := (selected_largest_free_prime_iff hr hp hc hs' hl).mp (by rw [he]; exact hrole)
  have hinterval := (selectedPrime_norm_interval (primary_ne_zero hr) (primary_ne_zero hc)
    (largestPrimeChoice d) a b).mp (by rw [he]; exact hint)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨mem_primaryElementBall.mpr ⟨hc,hcB⟩,
    mem_primeCutoff.mpr ⟨hp,hpB⟩⟩,hsrc,hrce,?_⟩
  unfold stoppedSelectedPrimeSet
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨mem_primeCutoff.mpr ⟨hp,hpB⟩,hinterval⟩,hpcre⟩,
      hlarge,?_⟩,?_⟩
  · simpa only [hfull] using hbin
  · simpa only [he] using hstop

lemma selectedStopped_backward (B ρ a b : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    {r e : Eisenstein} (hr : primary r) (hbB : b ≤ B) {t : Eisenstein × Eisenstein}
    (ht : t ∈ selectedStoppedRowPairs B ρ a b j j₀ k h Z Q early r e) :
    t.2*t.1 ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e ∧
      (largestPrimeRemainder (t.2*t.1),largestPrimeChoice (t.2*t.1)) = t := by
  obtain ⟨ht,hsrc,hrce,hrow⟩ := Finset.mem_filter.mp ht
  obtain ⟨hc,hp⟩ := Finset.mem_product.mp ht
  obtain ⟨hc,_⟩ := mem_primaryElementBall.mp hc
  obtain ⟨hp,hpB⟩ := mem_primeCutoff.mp hp
  obtain ⟨hrow,hstop⟩ := Finset.mem_filter.mp hrow
  obtain ⟨hrow,hlarge,hbin⟩ := Finset.mem_filter.mp hrow
  obtain ⟨hrow,hpc⟩ := Finset.mem_filter.mp hrow
  obtain ⟨_,hint⟩ := Finset.mem_filter.mp hrow
  have hsfull := (selectedPrime_product_conditions r t.2 t.1 e hp).mpr ⟨hsrc,hrce,hpc⟩
  have hsc : Squarefree t.1 := (squarefree_mul_iff.mp hsrc).2.2
  have hpc' : ¬t.2 ∣ t.1 := fun hh => hp.2.not_isUnit (hpc.of_mul_right_left.isUnit_of_dvd hh)
  have hl := largestPrimePredicate_complement hr hc hlarge
  have hcan := largestPrimeChoice_prime_mul hp hc hsc hpc' hl
  have hne : (primaryPrimeFactors (t.2*t.1)).Nonempty := by
    rw [primaryPrimeFactors_prime_mul hp hc hsc hpc']
    exact Finset.insert_nonempty _ _
  have hrole := (selected_largest_free_prime_iff hr hp hc hsfull.1 hl).mpr hlarge
  have hfull : largestPrimeChoice (r*(t.2*t.1)) = t.2 :=
    ((largestPrimeChoice_dvd_right_iff hr (primary_mul hp.1 hc) hne).mp hrole).trans hcan.1
  have hint' := (selectedPrime_norm_interval (primary_ne_zero hr) (primary_ne_zero hc)
    t.2 a b).mpr hint
  have hdB : norm (t.2*t.1) ≤ B :=
    (norm_le_of_dvd_nonzero (primary_ne_zero (primary_mul hr (primary_mul hp.1 hc)))
      ⟨r,by ring⟩).trans (hint'.2.trans hbB)
  refine ⟨Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr ⟨primary_mul hp.1 hc,hdB⟩,
    hsfull.1,hne,hsfull.2,hint',hrole,?_,hstop⟩,?_⟩
  · simpa only [hfull] using hbin
  · exact Prod.ext hcan.2 hcan.1

/-- Every original selected-divisor term occurs exactly once. -/
theorem selectedStopped_sum_reindex (B ρ a b : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ)
    (early : Bool) (r e : Eisenstein) (hr : primary r) (hbB : b ≤ B)
    (F : Eisenstein → ℂ) :
    (∑ d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e, F d) =
      ∑ t ∈ selectedStoppedRowPairs B ρ a b j j₀ k h Z Q early r e, F (t.2*t.1) := by
  apply Finset.sum_bij (fun d _ => (largestPrimeRemainder d,largestPrimeChoice d))
  · intro d hd
    exact selectedStopped_forward B ρ a b j j₀ k h Z Q early hr hd
  · intro d hd d' hd' heq
    have hprop := (Finset.mem_filter.mp hd).2
    have hprop' := (Finset.mem_filter.mp hd').2
    have hcan := largestPrimeChoice_decomposition (mem_primaryElementBall.mp (Finset.mem_filter.mp hd).1).1
      (squarefree_mul_iff.mp hprop.1).2.2 hprop.2.1
    have hcan' := largestPrimeChoice_decomposition (mem_primaryElementBall.mp (Finset.mem_filter.mp hd').1).1
      (squarefree_mul_iff.mp hprop'.1).2.2 hprop'.2.1
    have hm := congrArg (fun t : Eisenstein × Eisenstein => t.2*t.1) heq
    exact hcan.2.2.2.2.1.symm.trans (hm.trans hcan'.2.2.2.2.1)
  · intro t ht
    exact ⟨t.2*t.1,(selectedStopped_backward B ρ a b j j₀ k h Z Q early hr hbB ht).1,
      (selectedStopped_backward B ρ a b j j₀ k h Z Q early hr hbB ht).2⟩
  · intro d hd
    have hp := (Finset.mem_filter.mp hd).2
    have hcan := largestPrimeChoice_decomposition (mem_primaryElementBall.mp (Finset.mem_filter.mp hd).1).1
      (squarefree_mul_iff.mp hp.1).2.2 hp.2.1
    exact congrArg F hcan.2.2.2.2.1.symm

end CubicFirstMoment

end

end OAI
