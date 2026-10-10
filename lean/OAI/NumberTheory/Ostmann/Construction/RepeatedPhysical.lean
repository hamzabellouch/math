import OAI.NumberTheory.Ostmann.Construction.RepeatedPrimeGroups

namespace OAI

noncomputable section
namespace Ostmann.Construction
open scoped BigOperators FourierTransform
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma tupleDistinctPrimes_prime [DecidableEq ι] (p : ι → ℕ) (hp : ∀i,(p i).Prime)
    (q : ↥(tupleDistinctPrimes p)) : (q:ℕ).Prime := by
  obtain ⟨i,hi,hqi⟩ := Finset.mem_image.mp q.property
  exact hqi ▸ hp i

omit [DecidableEq ι] in
theorem centered_grouped_mean_norm_le [DecidableEq ι] (p : ι → ℕ)
    [∀q:↥(tupleDistinctPrimes p),NeZero (q:ℕ)]
    (F : ι → (q : ℕ) → ZMod q → ℂ)
    (hzero : ∀q:↥(tupleDistinctPrimes p),∀i,∑x:ZMod (q:ℕ),F i q x=0)
    (hF : ∀q:↥(tupleDistinctPrimes p),∀i,(∑x:ZMod (q:ℕ),‖F i q x‖^2)≤(q:ℝ)) :
    ‖∏q:↥(tupleDistinctPrimes p),(∑x:ZMod (q:ℕ),groupedLocalTest p F q x)/(q:ℂ)‖≤
      Real.sqrt (∏i,p i:ℕ)/(∏q:↥(tupleDistinctPrimes p),(q:ℕ):ℕ) := by
  by_cases hsingle : ∃q:↥(tupleDistinctPrimes p),(tuplePrimeFiber p q).card=1
  · obtain ⟨q,hq⟩ := hsingle
    have hz : (∏q:↥(tupleDistinctPrimes p),(∑x:ZMod (q:ℕ),groupedLocalTest p F q x)/(q:ℂ))=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ q)
      rw [groupedLocalTest_sum_zero_singleton p F hq (hzero q),zero_div]
    rw [hz,norm_zero]
    exact div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  · apply grouped_mean_norm_le p F
    · intro q
      have hp := Finset.card_pos.mpr (tuplePrimeFiber_nonempty p q.property)
      have hn : (tuplePrimeFiber p q).card≠1 := fun h => hsingle ⟨q,h⟩
      omega
    · exact hF

theorem centered_tuple_physical_bound (p : ι → ℕ) (hp : ∀i,(p i).Prime)
    [∀q:↥(tupleDistinctPrimes p),NeZero (q:ℕ)]
    (F : ι → (q : ℕ) → ZMod q → ℂ)
    (hzero : ∀q:↥(tupleDistinctPrimes p),∀i,∑x:ZMod (q:ℕ),F i q x=0)
    (hF : ∀q:↥(tupleDistinctPrimes p),∀i,(∑x:ZMod (q:ℕ),‖F i q x‖^2)≤(q:ℝ))
    {X : ℝ} (hX : 0<X)
    (hperiod : ((∏q:↥(tupleDistinctPrimes p),(q:ℕ):ℕ):ℝ)/4<X) :
    ‖(∑'n:ℤ,(∏i,F i (p i) (n:ZMod (p i)))*SchwartzCutoff.psi ((n:ℝ)/X))/(Real.sqrt X:ℂ)‖≤
      Real.sqrt X*‖𝓕 SchwartzCutoff.psi 0‖*
        (Real.sqrt (∏i,p i:ℕ)/(∏q:↥(tupleDistinctPrimes p),(q:ℕ):ℕ)) := by
  have hcop : Pairwise (fun q r : ↥(tupleDistinctPrimes p) => (q:ℕ).Coprime (r:ℕ)) := by
    intro q r hqr
    apply (Nat.coprime_primes (tupleDistinctPrimes_prime p hp q) (tupleDistinctPrimes_prime p hp r)).mpr
    exact fun h => hqr (Subtype.ext h)
  have hQ : 0<∏q:↥(tupleDistinctPrimes p),(q:ℕ) :=
    Finset.prod_pos fun q _ => NeZero.pos (q:ℕ)
  let : NeZero (∏q:↥(tupleDistinctPrimes p),(q:ℕ)) := ⟨hQ.ne'⟩
  have hpoisson := crt_cutoff_residue_mean (fun q:↥(tupleDistinctPrimes p) => (q:ℕ)) hcop
    (fun q => groupedLocalTest p F q) hX hperiod
  simp_rw [groupedLocalTest_product] at hpoisson
  rw [hpoisson,norm_div,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hX,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg X)]
  have hsqrt : X/Real.sqrt X=Real.sqrt X := by
    apply (div_eq_iff (Real.sqrt_pos.mpr hX).ne').mpr
    exact (Real.mul_self_sqrt hX.le).symm
  rw [mul_div_right_comm,mul_div_right_comm,hsqrt]
  exact mul_le_mul_of_nonneg_left (centered_grouped_mean_norm_le p F hzero hF)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))

end Ostmann.Construction

end

end OAI
