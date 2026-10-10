import OAI.NumberTheory.TwoPoint.Bounds.LocalExpansion

namespace OAI

/-!
# Finite multiplicative expansion of a dilation

This is the arithmetic content of manuscript Lemma `lem:affine-dilation`.
The equality is asserted for positive arguments, the domain relevant to
ordinary multiplicative functions. No complete multiplicativity is used.
-/

open scoped BigOperators

namespace TwoPointCorrelations

/-- Extend `f(m/a)` by zero away from multiples of `a`. -/
noncomputable def dilate (a : ℕ) (f : ℕ → ℂ) (m : ℕ) : ℂ :=
  if a ∣ m then f (m / a) else 0

noncomputable def dilationLocal (a : ℕ) (f : ℕ → ℂ) (p k : ℕ) : ℂ :=
  if k < a.factorization p then 0 else f (p ^ (k - a.factorization p))

noncomputable def dilationB (a : ℕ) (f : ℕ → ℂ) (p k : ℕ) : ℂ :=
  if k = 0 then 1 else dilationLocal a f p k

noncomputable def dilationC (_a : ℕ) (_f : ℕ → ℂ) (_p k : ℕ) : ℂ :=
  if k = 0 then 1 else 0

noncomputable def dilationComponent (a : ℕ) (f : ℕ → ℂ) (E : Finset ℕ) : ℕ → ℂ :=
  localComponent f (dilationB a f) (dilationC a f) a.primeFactors E

theorem dilationLocal_eq_sub (a : ℕ) (f : ℕ → ℂ) {p : ℕ}
    (hp : p ∈ a.primeFactors) (k : ℕ) :
    dilationLocal a f p k = dilationB a f p k - dilationC a f p k := by
  have hpos : 0 < a.factorization p := by
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  by_cases hk : k = 0
  · subst k
    simp [dilationLocal, dilationB, dilationC, hpos]
  · simp [dilationB, dilationC, hk]

theorem dilate_eq_local_product (a : ℕ) (f : ℕ → ℂ)
    (ha : 0 < a) (hf : Multiplicative f) (h1 : f 1 = 1)
    {n : ℕ} (hn : 0 < n) :
    dilate a f n =
      (∏ p ∈ a.primeFactors, dilationLocal a f p (n.factorization p)) *
        ∏ p ∈ n.primeFactors \ a.primeFactors, f (p ^ n.factorization p) := by
  classical
  by_cases hd : a ∣ n
  · have hle : a.factorization ≤ n.factorization :=
      (Nat.factorization_le_iff_dvd ha.ne' hn.ne').mpr hd
    have hsupport : (n / a).factorization.support ⊆ a.primeFactors ∪ n.primeFactors := by
      intro p hp
      apply Finset.mem_union.mpr
      right
      change p ∈ n.factorization.support
      apply Finsupp.mem_support_iff.mpr
      have hp' := Finsupp.mem_support_iff.mp hp
      simp only [Nat.factorization_div hd, Finsupp.tsub_apply] at hp'
      omega
    have hprod := fromPrimePowers_reconstruct f hf h1
      (Nat.div_pos (Nat.le_of_dvd hn hd) ha)
    rw [dilate, ite_eq_left_iff.mpr (fun h => (h hd).elim), ← hprod]
    unfold fromPrimePowers
    rw [Finsupp.prod_of_support_subset _ hsupport _ (by intro p _; simp [h1])]
    rw [← Finset.union_sdiff_self_eq_union (s := a.primeFactors) (t := n.primeFactors),
      Finset.prod_union disjoint_sdiff_self_left.symm]
    congr 1
    · apply Finset.prod_congr rfl
      intro p hp
      simp [dilationLocal, Nat.not_lt.mpr (hle p), Nat.factorization_div hd,
        Finsupp.tsub_apply]
    · apply Finset.prod_congr rfl
      intro p hp
      have hp0 : a.factorization p = 0 :=
        Finsupp.notMem_support_iff.mp (Finset.mem_sdiff.mp hp).2
      simp [Nat.factorization_div hd, Finsupp.tsub_apply, hp0]
  · have hex : ∃ p, n.factorization p < a.factorization p := by
      by_contra! h
      apply hd
      exact (Nat.factorization_le_iff_dvd ha.ne' hn.ne').mp (Finsupp.le_def.mpr h)
    obtain ⟨p, hp⟩ := hex
    have hpP : p ∈ a.primeFactors := by
      change p ∈ a.factorization.support
      apply Finsupp.mem_support_iff.mpr
      omega
    simp only [dilate, hd, ite_false]
    rw [Finset.prod_eq_zero hpP (by simp [dilationLocal, hp])]
    simp

/-- A fixed dilation is a finite signed sum of normalized ordinary
multiplicative functions, even at arguments with nonunit residue classes. -/
theorem dilate_eq_sum_components (a : ℕ) (f : ℕ → ℂ)
    (ha : 0 < a) (hf : Multiplicative f) (h1 : f 1 = 1)
    {n : ℕ} (hn : 0 < n) :
    dilate a f n = ∑ E ∈ a.primeFactors.powerset,
      (-1 : ℂ) ^ E.card * dilationComponent a f E n := by
  rw [dilate_eq_local_product a f ha hf h1 hn]
  rw [show (∏ p ∈ a.primeFactors, dilationLocal a f p (n.factorization p)) =
    ∏ p ∈ a.primeFactors, (dilationB a f p (n.factorization p) -
      dilationC a f p (n.factorization p)) from
    Finset.prod_congr rfl (fun p hp => dilationLocal_eq_sub a f hp _)]
  exact local_difference_expansion f (dilationB a f) (dilationC a f) a.primeFactors h1
    (by intro p; simp [dilationB]) (by intro p; simp [dilationC]) n

theorem dilationComponent_multiplicative (a : ℕ) (f : ℕ → ℂ) (E : Finset ℕ) :
    Multiplicative (dilationComponent a f E) :=
  localComponent_multiplicative _ _ _ _ _

@[simp] theorem dilationComponent_one (a : ℕ) (f : ℕ → ℂ) (E : Finset ℕ) :
    dilationComponent a f E 1 = 1 := by
  simp [dilationComponent, localComponent]

theorem dilationB_bound (a : ℕ) (f : ℕ → ℂ) (hf : OneBounded f)
    {p k : ℕ} (hp : p ∈ a.primeFactors) : ‖dilationB a f p k‖ ≤ 1 := by
  have hpos := (Nat.prime_of_mem_primeFactors hp).pos
  unfold dilationB dilationLocal
  split_ifs
  · simp
  · simp
  · exact hf _ (pow_pos hpos _)

theorem dilationComponent_oneBounded (a : ℕ) (f : ℕ → ℂ) (E : Finset ℕ)
    (hf : OneBounded f) : OneBounded (dilationComponent a f E) := by
  apply localComponent_oneBounded _ _ _ _ _ hf
  · intro p k hp _
    exact dilationB_bound a f hf hp
  · intro p k _ hk
    simp [dilationC, Nat.ne_of_gt hk]

theorem dilationComponent_nonpretentious (a : ℕ) (f : ℕ → ℂ) (E : Finset ℕ)
    (hf : OneBounded f) (hfnp : UniformlyNonpretentious f) :
    UniformlyNonpretentious (dilationComponent a f E) := by
  apply localComponent_nonpretentious _ _ _ _ _ hfnp hf
  · intro p k hp _
    exact dilationB_bound a f hf hp
  · intro p k _ hk
    simp [dilationC, Nat.ne_of_gt hk]

/-- Outside the dilation primes, the components keep the full prime-power
sequence of the original function. -/
theorem dilationComponent_prime_pow (a : ℕ) (f : ℕ → ℂ) (E : Finset ℕ)
    (h1 : f 1 = 1) {p : ℕ} (hp : p.Prime) (hpA : p ∉ a.primeFactors) (k : ℕ) :
    dilationComponent a f E (p ^ k) = f (p ^ k) := by
  unfold dilationComponent localComponent fromPrimePowers
  rw [hp.factorization_pow, Finsupp.prod_single_index]
  · simp [hpA]
  · simp [hpA, h1]

end TwoPointCorrelations

end OAI
