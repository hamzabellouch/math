import OAI.NumberTheory.CubicMoment.Estimates.RoughMoebius
import OAI.NumberTheory.CubicMoment.Estimates.SelectedPrimeCanonical

namespace OAI

/-! Exact primary factor-pair reindexing for a literal squarefree term.
The norm ball only makes the right-hand support finite. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Every subset of the actual prime factors gives one, and only one,
primary factor pair. This retains arbitrary weights on both factors. -/
theorem squarefree_primary_factor_pairs {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) {B : ℝ} (hnB : norm n ≤ B)
    (K : Eisenstein → Eisenstein → ℂ) :
    (∑ s ∈ (primaryPrimeFactors n).powerset,
      K (∏ p ∈ s, p) (∏ p ∈ primaryPrimeFactors n \ s, p)) =
    ∑ q ∈ ((primaryElementBall B).product (primaryElementBall B)).filter
        (fun q => q.1*q.2 = n), K q.1 q.2 := by
  let f : Finset Eisenstein → Eisenstein × Eisenstein :=
    fun s => ((∏ p ∈ s, p), (∏ p ∈ primaryPrimeFactors n \ s, p))
  have hfirst (s : Finset Eisenstein) (hsub : s ⊆ primaryPrimeFactors n) :
      primary (f s).1 :=
    primary_finset_prod s (fun p => p)
      (fun p hp => (primaryPrimeFactor_spec hn (hsub hp)).1.1)
  have hsecond (s : Finset Eisenstein) (hsub : s ⊆ primaryPrimeFactors n) :
      primary (f s).2 := by
    exact (primaryFactorRemainder_spec hn hs hsub).1
  have hmul (s : Finset Eisenstein) (hsub : s ⊆ primaryPrimeFactors n) :
      (f s).1*(f s).2 = n :=
    (primaryFactorRemainder_spec hn hs hsub).2.2
  apply Finset.sum_bij (fun s _ => f s)
  · intro s hsmem
    have hsub := Finset.mem_powerset.mp hsmem
    have hd : (f s).1 ∣ n := ⟨(f s).2,(hmul s hsub).symm⟩
    have he : (f s).2 ∣ n := ⟨(f s).1,by simpa only [mul_comm] using (hmul s hsub).symm⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr
      ⟨mem_primaryElementBall.mpr ⟨hfirst s hsub,
        (norm_le_of_dvd (primary_ne_zero hn) hd).trans hnB⟩,
       mem_primaryElementBall.mpr ⟨hsecond s hsub,
        (norm_le_of_dvd (primary_ne_zero hn) he).trans hnB⟩⟩,
      hmul s hsub⟩
  · intro s hsmem t htmem heq
    have hs' := Finset.mem_powerset.mp hsmem
    have ht' := Finset.mem_powerset.mp htmem
    have hh := congrArg primaryPrimeFactors (congrArg Prod.fst heq)
    change primaryPrimeFactors (∏ p ∈ s, p) = primaryPrimeFactors (∏ p ∈ t, p) at hh
    rwa [primaryPrimeFactors_finset_prod s (fun p hp => (primaryPrimeFactor_spec hn (hs' hp)).1),
      primaryPrimeFactors_finset_prod t (fun p hp => (primaryPrimeFactor_spec hn (ht' hp)).1)] at hh
  · intro q hq
    obtain ⟨hqball,hqn⟩ := Finset.mem_filter.mp hq
    have ha := (mem_primaryElementBall.mp (Finset.mem_product.mp hqball).1).1
    have hb := (mem_primaryElementBall.mp (Finset.mem_product.mp hqball).2).1
    have hsq : Squarefree (q.1*q.2) := by rwa [hqn]
    have hsa : Squarefree q.1 := hsq.of_mul_left
    have hsb : Squarefree q.2 := hsq.of_mul_right
    have hcop : IsCoprime q.1 q.2 :=
      isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hsq).1
    have hdis : Disjoint (primaryPrimeFactors q.1) (primaryPrimeFactors q.2) := by
      apply Finset.disjoint_left.mpr
      intro p hp hp'
      have hpa := primaryPrimeFactor_spec ha hp
      have hpb := primaryPrimeFactor_spec hb hp'
      exact hpa.1.2.not_isUnit (hcop.isUnit_of_dvd' hpa.2 hpb.2)
    have hunion : primaryPrimeFactors n =
        primaryPrimeFactors q.1 ∪ primaryPrimeFactors q.2 := by
      rw [←hqn,primaryPrimeFactors_mul_union ha hb]
    have hsub : primaryPrimeFactors q.1 ⊆ primaryPrimeFactors n := by
      rw [hunion]
      exact Finset.subset_union_left
    have hrem : primaryPrimeFactors n \ primaryPrimeFactors q.1 = primaryPrimeFactors q.2 := by
      rw [hunion]
      ext p
      simp only [Finset.mem_sdiff,Finset.mem_union]
      constructor
      · rintro ⟨hp,hnot⟩
        exact hp.resolve_left hnot
      · intro hp
        exact ⟨Or.inr hp,fun hp' => Finset.disjoint_left.mp hdis hp' hp⟩
    refine ⟨primaryPrimeFactors q.1,Finset.mem_powerset.mpr hsub,?_⟩
    apply Prod.ext
    · exact primaryPrimeFactors_prod ha hsa
    · dsimp only [f]
      rw [hrem,primaryPrimeFactors_prod hb hsb]
  · intro s _hsmem
    rfl

/-- Arbitrary original support remains an exact product-support test
after collecting finite primary factor fibres. -/
theorem primary_pair_fiber_support (S : Finset Eisenstein) (B : ℝ)
    (K : Eisenstein → Eisenstein → ℂ) :
    (∑ n ∈ S,
      ∑ q ∈ ((primaryElementBall B).product (primaryElementBall B)).filter
        (fun q => q.1*q.2 = n), K q.1 q.2) =
    ∑ d ∈ primaryElementBall B, ∑ e ∈ primaryElementBall B,
      if d*e ∈ S then K d e else 0 := by
  rw [Finset.sum_fiberwise_eq_sum_filter,Finset.sum_filter,
    Finset.product_eq_sprod,Finset.sum_product]

/-- The product cutoff is retained literally when the finite product
fibres are collected. No condition on the pair weight is required. -/
theorem primary_pair_fiber_cutoff (B : ℝ) (K : Eisenstein → Eisenstein → ℂ) :
    (∑ n ∈ primaryElementBall B,
      ∑ q ∈ ((primaryElementBall B).product (primaryElementBall B)).filter
        (fun q => q.1*q.2 = n), K q.1 q.2) =
    ∑ d ∈ primaryElementBall B, ∑ e ∈ primaryElementBall B,
      if norm (d*e) ≤ B then K d e else 0 := by
  rw [Finset.sum_fiberwise_eq_sum_filter,Finset.sum_filter,
    Finset.product_eq_sprod,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  have hprim := primary_mul (mem_primaryElementBall.mp hd).1 (mem_primaryElementBall.mp he).1
  simp only [mem_primaryElementBall,hprim,true_and]

/-- Full finite reindexing of `(m, subset of its prime factors)` into
independent primary factor pairs. Squarefree support and the sharp product
cutoff remain explicit on the right-hand side. -/
theorem squarefree_primary_subset_cutoff_sum (B : ℝ)
    (K : Eisenstein → Eisenstein → ℂ) :
    (∑ n ∈ (primaryElementBall B).filter Squarefree,
      ∑ s ∈ (primaryPrimeFactors n).powerset,
        K (∏ p ∈ s, p) (∏ p ∈ primaryPrimeFactors n \ s, p)) =
    ∑ d ∈ primaryElementBall B, ∑ e ∈ primaryElementBall B,
      if Squarefree (d*e) ∧ norm (d*e) ≤ B then K d e else 0 := by
  calc
    _ = ∑ n ∈ primaryElementBall B,
        ∑ q ∈ ((primaryElementBall B).product (primaryElementBall B)).filter
          (fun q => q.1*q.2 = n),
            if Squarefree (q.1*q.2) then K q.1 q.2 else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hs : Squarefree n
      · simp only [hs,ite_true]
        rw [squarefree_primary_factor_pairs (mem_primaryElementBall.mp hn).1 hs
          (mem_primaryElementBall.mp hn).2]
        apply Finset.sum_congr rfl
        intro q hq
        have he := (Finset.mem_filter.mp hq).2
        simp only [he,hs,ite_true]
      · simp only [hs,ite_false]
        symm
        apply Finset.sum_eq_zero
        intro q hq
        have he := (Finset.mem_filter.mp hq).2
        simp only [he,hs,ite_false]
    _ = ∑ d ∈ primaryElementBall B, ∑ e ∈ primaryElementBall B,
        if norm (d*e) ≤ B then (if Squarefree (d*e) then K d e else 0) else 0 :=
      primary_pair_fiber_cutoff B (fun d e => if Squarefree (d*e) then K d e else 0)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _hd
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hs : Squarefree (d*e) <;> simp [hs]

end CubicFirstMoment

end

end OAI
