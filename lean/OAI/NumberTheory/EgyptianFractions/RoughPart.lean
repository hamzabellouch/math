import OAI.NumberTheory.EgyptianFractions.LargePrimeDivisors

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The part of an integer supported on primes at least `R`, retaining their
full multiplicities. The definition at zero is harmlessly the empty product. -/
def roughPart (R : ℝ) (n : ℕ) : ℕ :=
  (n.primeFactorsList.filter (fun p : ℕ => R ≤ (p : ℝ))).prod

theorem roughPart_pos (R : ℝ) (n : ℕ) : 0 < roughPart R n := by
  apply List.prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primeFactorsList (List.mem_filter.mp hp).1).pos

theorem roughPart_dvd (R : ℝ) {n : ℕ} (hn : n ≠ 0) : roughPart R n ∣ n := by
  have h := (List.filter_sublist
    (p := fun p : ℕ => decide (R ≤ (p : ℝ))) (l := n.primeFactorsList)).prod_dvd_prod
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by simpa only [roughPart, Nat.prod_primeFactorsList hn] using hk⟩

theorem roughPart_le (R : ℝ) {n : ℕ} (hn : n ≠ 0) : roughPart R n ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (roughPart_dvd R hn)

theorem roughPart_log_le (R : ℝ) {n : ℕ} (hn : n ≠ 0) :
    Real.log (roughPart R n : ℝ) ≤ Real.log (n : ℝ) := by
  exact Real.log_le_log (by exact_mod_cast roughPart_pos R n)
    (by exact_mod_cast roughPart_le R hn)

theorem roughPart_primeFactorsList (R : ℝ) (n : ℕ) :
    (n.primeFactorsList.filter (fun p : ℕ => R ≤ (p : ℝ))).Perm
      (roughPart R n).primeFactorsList := by
  exact Nat.primeFactorsList_unique rfl (fun p hp =>
    Nat.prime_of_mem_primeFactorsList (List.mem_filter.mp hp).1)

theorem roughPart_large (R : ℝ) (n : ℕ) :
    ∀ p ∈ (roughPart R n).primeFactorsList, R ≤ (p : ℝ) := by
  intro p hp
  have h := (roughPart_primeFactorsList R n).mem_iff.mpr hp
  exact of_decide_eq_true (List.mem_filter.mp h).2

/-- Divisibility in the rough part is exactly divisibility in the original
integer together with the roughness of the divisor, not of the ambient integer. -/
theorem dvd_roughPart_iff (R : ℝ) {n d : ℕ} (hn : n ≠ 0) :
    d ∣ roughPart R n ↔ d ∣ n ∧ ∀ p ∈ d.primeFactorsList, R ≤ (p : ℝ) := by
  constructor
  · intro hd
    refine ⟨hd.trans (roughPart_dvd R hn), ?_⟩
    intro p hp
    exact roughPart_large R n p
      (Nat.primeFactorsList_subset_of_dvd hd (roughPart_pos R n).ne' hp)
  · rintro ⟨hd, hlarge⟩
    have hd0 : d ≠ 0 := (Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hn)).ne'
    have hsub := List.Sublist.filter (fun p : ℕ => decide (R ≤ (p : ℝ)))
      (Nat.primeFactorsList_sublist_of_dvd hd hn)
    have hfilter : d.primeFactorsList.filter (fun p : ℕ => R ≤ (p : ℝ)) =
        d.primeFactorsList := by
      apply List.filter_eq_self.mpr
      intro p hp
      exact decide_eq_true (hlarge p hp)
    have h := hsub.prod_dvd_prod
    rw [hfilter, Nat.prod_primeFactorsList hd0] at h
    exact h

/-- Exact finite-set transport, including all repeated prime powers. -/
theorem rough_divisors_eq_roughPart_divisors (R X : ℝ) {n : ℕ} (hn : n ≠ 0) :
    n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ X ∧
      ∀ p ∈ d.primeFactorsList, R ≤ (p : ℝ)) =
    (roughPart R n).divisors.filter (fun d : ℕ => (d : ℝ) ≤ X) := by
  classical
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, _⟩, hX, hR⟩
    exact ⟨⟨(dvd_roughPart_iff R hn).mpr ⟨hd, hR⟩, (roughPart_pos R n).ne'⟩, hX⟩
  · rintro ⟨⟨hd, _⟩, hX⟩
    obtain ⟨hdn, hR⟩ := (dvd_roughPart_iff R hn).mp hd
    exact ⟨⟨hdn, hn⟩, hX, hR⟩

/-- Any finite family of rough divisors is bounded by the existing truncated
count of the single rough part. This is the transport needed for differences
of samples, whose small prime factors must not be excluded. -/
theorem rough_divisor_card_le_truncated_roughPart (R X : ℝ) {n : ℕ}
    (hn : n ≠ 0) (s : Finset ℕ)
    (hdiv : ∀ d ∈ s, d ∣ n)
    (hsmall : ∀ d ∈ s, (d : ℝ) ≤ X)
    (hrough : ∀ d ∈ s, ∀ p ∈ d.primeFactorsList, R ≤ (p : ℝ)) :
    s.card ≤ truncatedDivisorCount X (roughPart R n) := by
  classical
  apply Finset.card_le_card
  intro d hd
  exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
    ⟨(dvd_roughPart_iff R hn).mpr ⟨hdiv d hd, hrough d hd⟩,
      (roughPart_pos R n).ne'⟩, hsmall d hd⟩

end Problem337

end

end OAI
