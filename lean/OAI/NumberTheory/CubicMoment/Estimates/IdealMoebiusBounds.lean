import OAI.NumberTheory.CubicMoment.Estimates.ShortMoebius

namespace OAI

/-! Finite Euler products identify and bound the arithmetic Möbius coefficients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

def finiteIdealMoebius (S : Finset EisensteinIdealPrime) : EisensteinArithmeticFunction :=
  ∏ p ∈ S, (1 - MvPowerSeries.X p)

private lemma coeff_mul_one_sub_X (A : EisensteinArithmeticFunction)
    (p : EisensteinIdealPrime) (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν (A * (1 - MvPowerSeries.X p)) =
      MvPowerSeries.coeff ν A -
        if 1 ≤ ν p then MvPowerSeries.coeff (ν - Finsupp.single p 1) A else 0 := by
  rw [mul_sub, mul_one, map_sub, MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial]
  simp only [Finsupp.single_le_iff, mul_one]

private lemma tsub_single_away (S : Finset EisensteinIdealPrime)
    {p : EisensteinIdealPrime} (hp : p ∉ S) (ν : EisensteinIdealExponent) :
    (∀ q ∈ S, (ν - Finsupp.single p 1 : EisensteinIdealExponent) q = 0) ↔ ∀ q ∈ S, ν q = 0 := by
  apply forall₂_congr
  intro q hq
  simp [Finsupp.tsub_apply, ne_of_mem_of_not_mem hq hp]

/-- Multiplying the zeta series by a finite Euler product excludes
precisely the prime divisors occurring in that product. -/
lemma coeff_zeta_finiteIdealMoebius (S : Finset EisensteinIdealPrime)
    (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν (idealZeta * finiteIdealMoebius S) =
      if ∀ p ∈ S, ν p = 0 then 1 else 0 := by
  induction S using Finset.induction_on generalizing ν with
  | empty => simp [finiteIdealMoebius, idealZeta, MvPowerSeries.coeff_apply]
  | @insert p S hp ih =>
    have he : idealZeta * finiteIdealMoebius (insert p S) =
        (idealZeta * finiteIdealMoebius S) * (1 - MvPowerSeries.X p) := by
      rw [finiteIdealMoebius, Finset.prod_insert hp]
      unfold finiteIdealMoebius
      ring
    rw [he, coeff_mul_one_sub_X, ih, ih]
    simp only [tsub_single_away S hp, Finset.forall_mem_insert]
    by_cases h : ν p = 0
    · simp [h]
    · have hn : 1 ≤ ν p := Nat.one_le_iff_ne_zero.mpr h
      simp [h, hn]

/-- For a coefficient whose prime support lies in `S`, the genuine
Dirichlet inverse is computed by the finite Euler product over `S`. -/
lemma coeff_idealMoebiusSeries_eq_finite (S : Finset EisensteinIdealPrime)
    (ν : EisensteinIdealExponent) (hν : ν.support ⊆ S) :
    MvPowerSeries.coeff ν idealMoebiusSeries =
      MvPowerSeries.coeff ν (finiteIdealMoebius S) := by
  have he : idealMoebiusSeries * (idealZeta * finiteIdealMoebius S) =
      finiteIdealMoebius S := by
    rw [← mul_assoc, idealMoebiusSeries_mul_zeta, one_mul]
  rw [← he, MvPowerSeries.coeff_mul]
  symm
  rw [Finset.sum_eq_single (ν, 0)]
  · simp [coeff_zeta_finiteIdealMoebius]
  · intro a ha hne
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp ha
    have hle : a.2 ≤ ν := by
      rw [← hsum]
      exact le_add_of_nonneg_left zero_le
    have hz : ¬ ∀ p ∈ S, a.2 p = 0 := by
      intro hzero
      have ha2 : a.2 = 0 := by
        ext p
        by_cases hp : p ∈ S
        · exact hzero p hp
        · have hn : ν p = 0 := Finsupp.notMem_support_iff.mp (fun h => hp (hν h))
          exact Nat.eq_zero_of_le_zero (hn ▸ hle p)
      have ha1 : a.1 = ν := by simpa [ha2] using hsum
      exact hne (Prod.ext ha1 ha2)
    rw [coeff_zeta_finiteIdealMoebius, ite_eq_right hz, mul_zero]
  · intro h
    exact (h (Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_zero ν))).elim

private lemma finiteIdealMoebius_coeff_outside (S : Finset EisensteinIdealPrime)
    (ν : EisensteinIdealExponent) {q : EisensteinIdealPrime} (hq : q ∉ S)
    (hνq : ν q ≠ 0) :
    MvPowerSeries.coeff ν (finiteIdealMoebius S) = 0 := by
  induction S using Finset.induction_on generalizing ν with
  | empty =>
    have hν : ν ≠ 0 := by
      intro h
      exact hνq (congrArg (fun f : EisensteinIdealExponent => f q) h)
    simp [finiteIdealMoebius, MvPowerSeries.coeff_one, hν]
  | @insert p S hp ih =>
    have hqp : q ≠ p := fun h => hq (h ▸ Finset.mem_insert_self p S)
    have hqS : q ∉ S := fun h => hq (Finset.mem_insert_of_mem h)
    have he : finiteIdealMoebius (insert p S) =
        finiteIdealMoebius S * (1 - MvPowerSeries.X p) := by
      rw [finiteIdealMoebius, Finset.prod_insert hp]
      unfold finiteIdealMoebius
      ring
    rw [he, coeff_mul_one_sub_X, ih ν hqS hνq]
    by_cases hn : 1 ≤ ν p
    · rw [ite_eq_left hn, ih _ hqS]
      · simp
      · simpa [Finsupp.tsub_apply, hqp] using hνq
    · simp [hn]

private lemma finiteIdealMoebius_coeff_repeated (S : Finset EisensteinIdealPrime)
    (ν : EisensteinIdealExponent) {q : EisensteinIdealPrime} (hνq : 2 ≤ ν q) :
    MvPowerSeries.coeff ν (finiteIdealMoebius S) = 0 := by
  induction S using Finset.induction_on generalizing ν with
  | empty =>
    have hν : ν ≠ 0 := by
      intro h
      have hq := congrArg (fun f : EisensteinIdealExponent => f q) h
      simp only [Finsupp.zero_apply] at hq
      omega
    simp [finiteIdealMoebius, MvPowerSeries.coeff_one, hν]
  | @insert p S hp ih =>
    have he : finiteIdealMoebius (insert p S) =
        finiteIdealMoebius S * (1 - MvPowerSeries.X p) := by
      rw [finiteIdealMoebius, Finset.prod_insert hp]
      unfold finiteIdealMoebius
      ring
    rw [he, coeff_mul_one_sub_X]
    by_cases hqp : q = p
    · subst q
      rw [finiteIdealMoebius_coeff_outside S ν hp (by omega),
        ite_eq_left (by omega), finiteIdealMoebius_coeff_outside S _ hp]
      · simp
      · simpa only [Finsupp.tsub_apply, Finsupp.single_eq_same] using
          (show ν p - 1 ≠ 0 by omega)
    · rw [ih ν hνq]
      by_cases hn : 1 ≤ ν p
      · rw [ite_eq_left hn, ih _]
        · simp
        · simpa [Finsupp.tsub_apply, hqp] using hνq
      · simp [hn]

lemma idealMoebiusSeries_repeated {ν : EisensteinIdealExponent}
    {p : EisensteinIdealPrime} (hν : 2 ≤ ν p) :
    MvPowerSeries.coeff ν idealMoebiusSeries = 0 := by
  rw [coeff_idealMoebiusSeries_eq_finite ν.support ν (Finset.Subset.refl _)]
  exact finiteIdealMoebius_coeff_repeated _ _ hν

private lemma finiteIdealMoebius_coeff_squarefree (S : Finset EisensteinIdealPrime)
    (ν : EisensteinIdealExponent) (hν : ν.support ⊆ S) (h1 : ∀ p, ν p ≤ 1) :
    MvPowerSeries.coeff ν (finiteIdealMoebius S) = (-1 : ℝ) ^ ν.support.card := by
  induction S using Finset.induction_on generalizing ν with
  | empty =>
    have hz : ν = 0 := Finsupp.support_eq_empty.mp (Finset.subset_empty.mp hν)
    simp [hz, finiteIdealMoebius, MvPowerSeries.coeff_one]
  | @insert p S hp ih =>
    have he : finiteIdealMoebius (insert p S) =
        finiteIdealMoebius S * (1 - MvPowerSeries.X p) := by
      rw [finiteIdealMoebius, Finset.prod_insert hp]
      unfold finiteIdealMoebius
      ring
    rw [he, coeff_mul_one_sub_X]
    by_cases hz : ν p = 0
    · have hs : ν.support ⊆ S := by
        intro q hq
        rcases Finset.mem_insert.mp (hν hq) with h | h
        · subst q
          exact (Finsupp.mem_support_iff.mp hq hz).elim
        · exact h
      simpa [hz] using ih ν hs h1
    · have ho : ν p = 1 := by have := h1 p; omega
      let κ : EisensteinIdealExponent := ν - Finsupp.single p 1
      have hk : κ.support = ν.support.erase p := by
        ext q
        by_cases hqp : q = p
        · subst q
          simp [κ, Finsupp.mem_support_iff, Finsupp.tsub_apply, ho]
        · simp [κ, Finsupp.mem_support_iff, Finsupp.tsub_apply, hqp]
      have hκ : κ.support ⊆ S := by
        rw [hk]
        intro q hq
        rcases Finset.mem_erase.mp hq with ⟨hqp, hq⟩
        exact (Finset.mem_insert.mp (hν hq)).resolve_left hqp
      have hκ1 : ∀ q, κ q ≤ 1 := fun q =>
        (Nat.sub_le (ν q) _).trans (h1 q)
      have hcard : κ.support.card + 1 = ν.support.card := by
        rw [hk]
        exact Finset.card_erase_add_one (Finsupp.mem_support_iff.mpr hz)
      rw [finiteIdealMoebius_coeff_outside S ν hp hz, ite_eq_left (by omega),
        ih κ hκ hκ1, zero_sub, ← hcard, pow_succ]
      ring

lemma idealMoebiusSeries_squarefree {ν : EisensteinIdealExponent}
    (h1 : ∀ p, ν p ≤ 1) :
    MvPowerSeries.coeff ν idealMoebiusSeries = (-1 : ℝ) ^ ν.support.card := by
  rw [coeff_idealMoebiusSeries_eq_finite ν.support ν (Finset.Subset.refl _)]
  exact finiteIdealMoebius_coeff_squarefree _ _ (Finset.Subset.refl _) h1

lemma finiteIdealMoebius_coeff_abs_le_one (S : Finset EisensteinIdealPrime)
    (ν : EisensteinIdealExponent) :
    |MvPowerSeries.coeff ν (finiteIdealMoebius S)| ≤ 1 := by
  induction S using Finset.induction_on generalizing ν with
  | empty => simp [finiteIdealMoebius, MvPowerSeries.coeff_one]; split_ifs <;> norm_num
  | @insert p S hp ih =>
    have he : finiteIdealMoebius (insert p S) =
        finiteIdealMoebius S * (1 - MvPowerSeries.X p) := by
      rw [finiteIdealMoebius, Finset.prod_insert hp]
      unfold finiteIdealMoebius
      ring
    rw [he, coeff_mul_one_sub_X]
    by_cases hn : 1 ≤ ν p
    · rw [ite_eq_left hn, finiteIdealMoebius_coeff_outside S ν hp
        (Nat.ne_zero_of_lt hn), zero_sub, abs_neg]
      exact ih _
    · simpa [hn] using ih ν

/-- The actual Dirichlet-inverse Möbius coefficients have amplitude at most one. -/
lemma idealMoebiusSeries_abs_le_one (ν : EisensteinIdealExponent) :
    |MvPowerSeries.coeff ν idealMoebiusSeries| ≤ 1 := by
  rw [coeff_idealMoebiusSeries_eq_finite ν.support ν (Finset.Subset.refl _)]
  exact finiteIdealMoebius_coeff_abs_le_one _ _

lemma shortIdealMoebius_abs_le_one (F : ℝ) (ν : EisensteinIdealExponent) :
    |MvPowerSeries.coeff ν (shortIdealMoebius F)| ≤ 1 := by
  change |if idealExponentNorm ν ≤ Real.sqrt F then _ else (0 : ℝ)| ≤ 1
  split_ifs
  · exact idealMoebiusSeries_abs_le_one ν
  · norm_num

/-- Normalized prime representatives identify the exponent multiset
with the existing normalized factorization of an Eisenstein element. -/
lemma idealPrimeFactors_normalized (a : Eisenstein) :
    (Associates.factors' a).map (fun p => p.val.out) =
      UniqueFactorizationMonoid.normalizedFactors a := by
  calc
    _ = ((Associates.factors' a).map Subtype.val).map
        (Associates.out : Associates Eisenstein → Eisenstein) :=
      (Multiset.map_map _ _ _).symm
    _ = _ := by
      rw [Associates.map_subtype_coe_factors', Multiset.map_map]
      rfl

lemma idealExponentOf_squarefree_iff {a : Eisenstein} (ha : a ≠ 0) :
    (∀ p, idealExponentOf a p ≤ 1) ↔ Squarefree a := by
  rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors ha,
    ← idealPrimeFactors_normalized]
  have hinj : Function.Injective
      (fun p : EisensteinIdealPrime => p.val.out) :=
    Associates.out_injective.comp Subtype.val_injective
  rw [Multiset.nodup_map_iff_of_injective hinj, Multiset.nodup_iff_count_le_one]
  rfl

lemma idealExponentOf_support_card {a : Eisenstein} (ha : Squarefree a) :
    (idealExponentOf a).support.card = (UniqueFactorizationMonoid.factors a).card := by
  have hnodup : (Associates.factors' a).Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    exact (idealExponentOf_squarefree_iff ha.ne_zero).mpr ha
  change (Associates.factors' a).toFinset.card = _
  rw [Multiset.toFinset_card_of_nodup hnodup]
  have h := congrArg Multiset.card (Associates.map_subtype_coe_factors' (a := a))
  simpa only [Multiset.card_map] using h

/-- The Dirichlet-inverse definition agrees with the repository's
arithmetic Möbius function on every nonzero Eisenstein ideal. -/
lemma idealMoebiusSeries_at_element {a : Eisenstein} (ha : a ≠ 0) :
    MvPowerSeries.coeff (idealExponentOf a) idealMoebiusSeries = (idealMoebius a : ℝ) := by
  by_cases hs : Squarefree a
  · rw [idealMoebiusSeries_squarefree ((idealExponentOf_squarefree_iff ha).mpr hs),
      idealExponentOf_support_card hs]
    simp [idealMoebius, hs]
  · have hh : ¬ ∀ p, idealExponentOf a p ≤ 1 :=
      mt (idealExponentOf_squarefree_iff ha).mp hs
    push Not at hh
    obtain ⟨p, hp⟩ := hh
    rw [idealMoebiusSeries_repeated (by omega : 2 ≤ idealExponentOf a p)]
    simp [idealMoebius, hs]

lemma shortIdealMoebius_at_element (F : ℝ) {a : Eisenstein} (ha : a ≠ 0) :
    MvPowerSeries.coeff (idealExponentOf a) (shortIdealMoebius F) =
      if norm a ≤ Real.sqrt F then (idealMoebius a : ℝ) else 0 := by
  change (if idealExponentNorm (idealExponentOf a) ≤ Real.sqrt F then _ else _) = _
  rw [idealExponentOf_norm ha, idealMoebiusSeries_at_element ha]

lemma shortIdealMoebius_support {F : ℝ} {a : Eisenstein} (ha : a ≠ 0)
    (h : MvPowerSeries.coeff (idealExponentOf a) (shortIdealMoebius F) ≠ 0) :
    Squarefree a ∧ norm a ≤ Real.sqrt F := by
  rw [shortIdealMoebius_at_element F ha] at h
  by_cases hn : norm a ≤ Real.sqrt F
  · rw [ite_eq_left hn] at h
    refine ⟨?_, hn⟩
    by_contra hs
    simp [idealMoebius, hs] at h
  · simp [hn] at h

end CubicFirstMoment

end

end OAI
