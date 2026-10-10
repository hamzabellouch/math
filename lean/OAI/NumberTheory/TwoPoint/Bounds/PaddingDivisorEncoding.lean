import OAI.NumberTheory.TwoPoint.Bounds.PaddingLiteralBins

namespace OAI

/-! Squarefree padding divisors encode prime selections without multiplicity.
This identifies the bin law with the paper's numerical divisor sum. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def paddingAvailablePrimes (Q : Finset ℕ) (a : Q → Bool) : Finset ℕ :=
  (selectedCoordinates Q a).image Subtype.val

lemma paddingAvailablePrimes_subset (Q : Finset ℕ) (a : Q → Bool) :
    paddingAvailablePrimes Q a ⊆ Q := by
  intro p hp
  obtain ⟨u, _, rfl⟩ := mem_image.mp hp
  exact u.property

lemma mem_paddingAvailablePrimes (Q : Finset ℕ) (a : Q → Bool) (p : Q) :
    p.val ∈ paddingAvailablePrimes Q a ↔ a p = true := by
  constructor
  · intro hp
    obtain ⟨u, hu, he⟩ := mem_image.mp hp
    have hup : u = p := Subtype.ext he
    subst u
    exact (mem_filter.mp hu).2
  · intro hp
    exact mem_image.mpr ⟨p, mem_filter.mpr ⟨mem_univ p, hp⟩, rfl⟩

lemma paddingSelectedDivisor_eq_prod (Q : Finset ℕ) (b : Q → Bool) :
    paddingSelectedDivisor Q b = ∏ p ∈ paddingAvailablePrimes Q b, p := by
  rw [paddingAvailablePrimes, prod_image]
  · rfl
  · intro p _ q _ hpq
    exact Subtype.ext hpq

lemma paddingSelectedDivisor_primeFactors (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (b : Q → Bool) : (paddingSelectedDivisor Q b).primeFactors = paddingAvailablePrimes Q b := by
  rw [paddingSelectedDivisor_eq_prod, Nat.primeFactors_prod]
  exact fun p hp => hQ p (paddingAvailablePrimes_subset Q b hp)

lemma paddingAvailablePrimes_card (Q : Finset ℕ) (a : Q → Bool) :
    (paddingAvailablePrimes Q a).card = (selectedCoordinates Q a).card := by
  exact card_image_iff.mpr (fun _ _ _ _ h => Subtype.ext h)

lemma padding_supported_iff_primeFactors_subset (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (a b : Q → Bool) :
    PaddingSelectionSupported Q a b ↔
      (paddingSelectedDivisor Q b).primeFactors ⊆ paddingAvailablePrimes Q a := by
  rw [paddingSelectedDivisor_primeFactors Q hQ b]
  constructor
  · intro h p hp
    have hpQ := paddingAvailablePrimes_subset Q b hp
    exact (mem_paddingAvailablePrimes Q a ⟨p, hpQ⟩).mpr
      (h ⟨p, hpQ⟩ ((mem_paddingAvailablePrimes Q b ⟨p, hpQ⟩).mp hp))
  · intro h p hp
    exact (mem_paddingAvailablePrimes Q a p).mp
      (h ((mem_paddingAvailablePrimes Q b p).mpr hp))

lemma paddingSelectedDivisor_injective (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    Function.Injective (paddingSelectedDivisor Q) := by
  intro b c hbc
  have hsets : paddingAvailablePrimes Q b = paddingAvailablePrimes Q c := by
    simpa only [paddingSelectedDivisor_primeFactors Q hQ] using congrArg Nat.primeFactors hbc
  funext p
  have he : (b p = true) ↔ (c p = true) := by
    rw [← mem_paddingAvailablePrimes Q b p, ← mem_paddingAvailablePrimes Q c p, hsets]
  cases hb : b p <;> cases hc : c p <;> simp_all

lemma paddingSelectedDivisor_mem (Q : Finset ℕ) (b : Q → Bool) :
    paddingSelectedDivisor Q b ∈ retainedPrimeDivisors Q := by
  rw [retainedPrimeDivisors, paddingSelectedDivisor_eq_prod]
  exact mem_image.mpr ⟨paddingAvailablePrimes Q b,
    mem_powerset.mpr (paddingAvailablePrimes_subset Q b), rfl⟩

lemma exists_paddingSelection (Q : Finset ℕ) (q : ℕ) (hq : q ∈ retainedPrimeDivisors Q) :
    ∃ b : Q → Bool, paddingSelectedDivisor Q b = q := by
  obtain ⟨S, hS, rfl⟩ := mem_image.mp hq
  have hSQ := mem_powerset.mp hS
  let b : Q → Bool := fun p => decide (p.val ∈ S)
  have hb : paddingAvailablePrimes Q b = S := by
    ext p
    constructor
    · intro hp
      obtain ⟨u, hu, rfl⟩ := mem_image.mp hp
      simpa only [selectedCoordinates, mem_filter, mem_univ, true_and, b,
        decide_eq_true_eq] using hu
    · intro hp
      exact (mem_paddingAvailablePrimes Q b ⟨p, hSQ hp⟩).mpr (by simp [b, hp])
  exact ⟨b, by rw [paddingSelectedDivisor_eq_prod, hb]⟩

noncomputable def paddingDivisorEquiv (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    (Q → Bool) ≃ retainedPrimeDivisors Q :=
  Equiv.ofBijective (fun b => ⟨paddingSelectedDivisor Q b, paddingSelectedDivisor_mem Q b⟩)
    ⟨fun _ _ h => paddingSelectedDivisor_injective Q hQ (congrArg Subtype.val h), by
      intro q
      obtain ⟨b, hb⟩ := exists_paddingSelection Q q q.property
      exact ⟨b, Subtype.ext hb⟩⟩

/-- `rho_j` as a sum over actual numerical squarefree divisors. -/
noncomputable def literalPaddingBinMass (Q : Finset ℕ) (a : Q → Bool)
    (η c : ℝ) (j : ℤ) : ℝ :=
  (5 : ℝ) ^ (-(paddingAvailablePrimes Q a).card : ℤ) *
    ∑ q ∈ retainedPrimeDivisors Q,
      if q.primeFactors ⊆ paddingAvailablePrimes Q a ∧
          paddingBin η c (Real.log q) = j
      then (4 : ℝ) ^ q.primeFactors.card else 0

lemma paddingBinMass_eq_literal (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (a : Q → Bool) (η c : ℝ) (j : ℤ) :
    paddingBinMass Q a η c j = literalPaddingBinMass Q a η c j := by
  rw [paddingBinMass_normalized_sum, paddingTiltWeight_eq_five_pow]
  unfold literalPaddingBinMass
  rw [paddingAvailablePrimes_card, zpow_neg, zpow_natCast]
  congr 1
  let F (q : retainedPrimeDivisors Q) : ℝ :=
    if q.val.primeFactors ⊆ paddingAvailablePrimes Q a ∧
        paddingBin η c (Real.log q.val) = j
    then (4 : ℝ) ^ q.val.primeFactors.card else 0
  calc
    _ = ∑ b : Q → Bool, F (paddingDivisorEquiv Q hQ b) := by
      apply sum_congr rfl
      intro b _
      change _ = if (paddingSelectedDivisor Q b).primeFactors ⊆ paddingAvailablePrimes Q a ∧
        paddingBin η c (Real.log (paddingSelectedDivisor Q b)) = j
        then (4 : ℝ) ^ (paddingSelectedDivisor Q b).primeFactors.card else 0
      have hs := padding_supported_iff_primeFactors_subset Q hQ a b
      rw [paddingSelectedDivisor_primeFactors Q hQ b] at hs
      simp only [← hs,
        paddingSelectedDivisor_log Q hQ b, paddingSelectedDivisor_primeFactors Q hQ b,
        paddingAvailablePrimes_card, paddingDivisorCoefficient_eq_four_pow]
    _ = ∑ q : retainedPrimeDivisors Q, F q := (paddingDivisorEquiv Q hQ).sum_comp F
    _ = _ := by
      unfold F
      exact sum_coe_sort (retainedPrimeDivisors Q) (fun q : ℕ =>
        if q.primeFactors ⊆ paddingAvailablePrimes Q a ∧ paddingBin η c (Real.log q) = j
        then (4 : ℝ) ^ q.primeFactors.card else 0)

lemma paddingTiltNormalizer_eq_divisor_sum (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) :
    paddingTiltNormalizer Q =
      ∑ q ∈ retainedPrimeDivisors Q, (4 : ℝ) ^ q.primeFactors.card / (q : ℝ) := by
  unfold paddingTiltNormalizer
  rw [prod_coe_sort Q (fun p : ℕ => 1 + 4 / (p : ℝ))]
  simpa only [prod_const] using
    (retainedPrimeDivisors_weighted_mass Q hQ (fun _ => (4 : ℝ))).symm

lemma padding_divisor_weight_total (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (a : Q → Bool) :
    (∑ q ∈ retainedPrimeDivisors Q,
      if q.primeFactors ⊆ paddingAvailablePrimes Q a then (4 : ℝ) ^ q.primeFactors.card else 0) =
        paddingTiltWeight Q a := by
  let F (q : retainedPrimeDivisors Q) : ℝ :=
    if q.val.primeFactors ⊆ paddingAvailablePrimes Q a then (4 : ℝ) ^ q.val.primeFactors.card else 0
  have he (b : Q → Bool) : F (paddingDivisorEquiv Q hQ b) =
      (paddingDivisorLaw Q a).weight b * paddingTiltWeight Q a := by
    rw [padding_divisor_weight]
    change (if (paddingSelectedDivisor Q b).primeFactors ⊆ paddingAvailablePrimes Q a
      then (4 : ℝ) ^ (paddingSelectedDivisor Q b).primeFactors.card else 0) = _
    have hs := padding_supported_iff_primeFactors_subset Q hQ a b
    rw [paddingSelectedDivisor_primeFactors Q hQ b] at hs
    simp only [← hs,
      paddingSelectedDivisor_primeFactors Q hQ b, paddingAvailablePrimes_card,
      paddingDivisorCoefficient_eq_four_pow]
  calc
    _ = ∑ q : retainedPrimeDivisors Q, F q := (sum_coe_sort _ (fun q : ℕ =>
      if q.primeFactors ⊆ paddingAvailablePrimes Q a then (4 : ℝ) ^ q.primeFactors.card else 0)).symm
    _ = ∑ b : Q → Bool, F (paddingDivisorEquiv Q hQ b) :=
      ((paddingDivisorEquiv Q hQ).sum_comp F).symm
    _ = ∑ b : Q → Bool, (paddingDivisorLaw Q a).weight b * paddingTiltWeight Q a :=
      sum_congr rfl (fun b _ => he b)
    _ = paddingTiltWeight Q a := by
      rw [← sum_mul, (paddingDivisorLaw Q a).total, one_mul]

end TwoPointCorrelations

end OAI
