import OAI.NumberTheory.CubicMoment.Decomposition.StoppedPrimeIntervals
import OAI.NumberTheory.CubicMoment.Estimates.LargestPrimeSelection
import OAI.NumberTheory.CubicMoment.Estimates.ShortFactorMoments

namespace OAI

/-! Exact unordered largest-prime reindexing of finite squarefree primary
sums. The free-prime/complement representation has multiplicity one. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largestPrime_product_unique {p q c d : Eisenstein}
    (hp : primaryPrime p) (hq : primaryPrime q)
    (hc : primary c) (hd : primary d) (hsc : Squarefree c) (hsd : Squarefree d)
    (hpc : ¬p ∣ c) (hqd : ¬q ∣ d) (he : p*c = q*d)
    (hlp : largestPrimePredicate primeTieCode (primaryPrimeFactors c) p)
    (hlq : largestPrimePredicate primeTieCode (primaryPrimeFactors d) q) :
    p = q ∧ c = d := by
  have hfc := primaryPrimeFactors_prime_mul hp hc hsc hpc
  have hfd := primaryPrimeFactors_prime_mul hq hd hsd hqd
  have hset : insert p (primaryPrimeFactors c) = insert q (primaryPrimeFactors d) := by
    rw [←hfc,←hfd,he]
  have hpl : largestPrimePredicate primeTieCode (insert p (primaryPrimeFactors c)) p := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact Or.inr ⟨rfl,le_rfl⟩
    · exact hlp r hr
  have hql : largestPrimePredicate primeTieCode (insert p (primaryPrimeFactors c)) q := by
    rw [hset]
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact Or.inr ⟨rfl,le_rfl⟩
    · exact hlq r hr
  have hpq : p = q := largestPrime_unique primeTieCode_injective
    (Finset.mem_insert_self _ _) (hset.symm ▸ Finset.mem_insert_self _ _) hpl hql
  refine ⟨hpq,?_⟩
  subst q
  exact mul_left_cancel₀ hp.2.ne_zero he

/-- A finite nonsmooth sum has exactly one free-largest-prime term for
each original integer. Membership of the original support is retained. -/
theorem sum_largestPrime_reindex (D : Finset Eisenstein) (B : ℝ)
    (hD : ∀ d ∈ D, primary d ∧ Squarefree d ∧ norm d ≤ B)
    (hne : ∀ d ∈ D, (primaryPrimeFactors d).Nonempty)
    (F : Eisenstein → ℂ) :
    (∑ d ∈ D, F d) =
      ∑ t ∈ ((primeCutoff B) ×ˢ (primaryElementBall B)).filter
        (fun t => t.1*t.2 ∈ D ∧ ¬t.1 ∣ t.2 ∧
          largestPrimePredicate primeTieCode (primaryPrimeFactors t.2) t.1), F (t.1*t.2) := by
  have hsplit : ∀ d ∈ D, ∃ p c : Eisenstein, primaryPrime p ∧ primary c ∧ Squarefree c ∧
      ¬p ∣ c ∧ p*c = d ∧ largestPrimePredicate primeTieCode (primaryPrimeFactors c) p ∧
      normNat p = (primaryPrimeFactors d).sup normNat := by
    intro d hd
    exact primary_largest_prime_split (hD d hd).1 (hD d hd).2.1 (hne d hd)
  choose p c hp hc hs hcop he hl _hn using hsplit
  apply Finset.sum_bij (fun d hd => (p d hd,c d hd))
  · intro d hd
    have hdn : d ≠ 0 := primary_ne_zero (hD d hd).1
    have hpn : norm (p d hd) ≤ B :=
      (norm_le_of_dvd_nonzero hdn ⟨c d hd,(he d hd).symm⟩).trans (hD d hd).2.2
    have hcn : norm (c d hd) ≤ B :=
      (norm_le_of_dvd_nonzero hdn ⟨p d hd,by rw [mul_comm,he d hd]⟩).trans (hD d hd).2.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨mem_primeCutoff.mpr ⟨hp d hd,hpn⟩,mem_primaryElementBall.mpr ⟨hc d hd,hcn⟩⟩,
      by simpa only [he d hd] using And.intro hd (And.intro (hcop d hd) (hl d hd))⟩
  · intro d hd d' hd' heq
    have hprod := congrArg (fun t : Eisenstein × Eisenstein => t.1*t.2) heq
    simpa only [he d hd,he d' hd'] using hprod
  · intro t ht
    obtain ⟨ht,hcond⟩ := Finset.mem_filter.mp ht
    obtain ⟨htp,htc⟩ := Finset.mem_product.mp ht
    have hp' := (mem_primeCutoff.mp htp).1
    have hc' := (mem_primaryElementBall.mp htc).1
    have hs' : Squarefree t.2 := (squarefree_mul_iff.mp (hD _ hcond.1).2.1).2.2
    refine ⟨t.1*t.2,hcond.1,?_⟩
    have heq := largestPrime_product_unique (hp _ hcond.1) hp' (hc _ hcond.1) hc'
      (hs _ hcond.1) hs' (hcop _ hcond.1) hcond.2.1 (he _ hcond.1) (hl _ hcond.1) hcond.2.2
    exact Prod.ext heq.1 heq.2
  · intro d hd
    exact congrArg F (he d hd).symm

end CubicFirstMoment

end

end OAI
