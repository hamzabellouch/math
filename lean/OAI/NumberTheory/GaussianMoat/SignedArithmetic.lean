import OAI.NumberTheory.GaussianMoat.LatticeComponents

namespace OAI

universe uIota

namespace GaussianMoat

def PrimitiveDirection (v : GaussianInt) : Prop := IsCoprime v.re v.im

theorem int_multiple_of_determinant_zero {v w : GaussianInt}
    (hv : PrimitiveDirection v) (hvw : determinant v w = 0) :
    ∃ a : ℤ, w = (a : GaussianInt) * v := by
  obtain ⟨r, s, hrs⟩ := hv
  refine ⟨r * w.re + s * w.im, ?_⟩
  change v.re * w.im - v.im * w.re = 0 at hvw
  ext <;> simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_intCast,
    Zsqrtd.im_intCast, zero_mul, mul_zero, add_zero]
  · nlinarith [congrArg (fun x : ℤ => x * w.re) hrs,
      congrArg (fun x : ℤ => s * x) hvw]
  · nlinarith [congrArg (fun x : ℤ => x * w.im) hrs,
      congrArg (fun x : ℤ => r * x) hvw]

theorem exists_primitive_direction {w : GaussianInt} (hw : w ≠ 0) :
    ∃ v : GaussianInt, PrimitiveDirection v ∧ v ≠ 0 ∧
      ∃ a : ℤ, a ≠ 0 ∧ w = (a : GaussianInt) * v := by
  have hg := (Zsqrtd.gcd_pos_iff w).mpr hw
  obtain ⟨v, hv, hcop⟩ := Zsqrtd.exists_coprime_of_gcd_pos hg
  refine ⟨v, hcop, ?_, (Int.gcd w.re w.im : ℤ), by exact_mod_cast hg.ne', hv⟩
  intro h
  apply hw
  simp only [h, mul_zero] at hv
  exact hv

theorem norm_dvd_norm {a b : GaussianInt} (h : a ∣ b) : a.norm ∣ b.norm := by
  obtain ⟨u, rfl⟩ := h
  rw [Zsqrtd.norm_mul]
  exact dvd_mul_right _ _

theorem factor_dvd_integer_iff {p : ℕ} {π : GaussianInt} (hp : Nat.Prime p)
    (hπ : π.norm = (p : ℤ)) (a : ℤ) : π ∣ (a : GaussianInt) ↔ (p : ℤ) ∣ a := by
  have hp' : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  constructor
  · intro h
    have hn := norm_dvd_norm h
    rw [hπ, Zsqrtd.norm_intCast] at hn
    exact (hp'.dvd_mul.mp hn).elim id id
  · intro h
    have hd : π ∣ (p : GaussianInt) := by
      have he : (p : GaussianInt) = π * star π := by
        rw [← Zsqrtd.norm_eq_mul_conj, hπ]
        simp
      rw [he]
      exact dvd_mul_right _ _
    exact hd.trans (map_dvd (Int.castRingHom GaussianInt) h)

theorem not_both_factors_dvd_primitive {p : ℕ} {π v : GaussianInt}
    (hp : Nat.Prime p) (hpodd : p ≠ 2) (hπ : π.norm = (p : ℤ))
    (hv : PrimitiveDirection v) : ¬ (π ∣ v ∧ star π ∣ v) := by
  rintro ⟨h1, h2⟩
  have hs : π ∣ star v := by
    obtain ⟨u, hu⟩ := h2
    refine ⟨star u, ?_⟩
    simpa only [star_mul, star_star, mul_comm] using congrArg star hu
  have hreal : π ∣ ((2 * v.re : ℤ) : GaussianInt) := by
    have heq : ((2 * v.re : ℤ) : GaussianInt) = v + star v := by
      ext <;> simp
      ring
    rw [heq]
    exact dvd_add h1 hs
  have himag : π ∣ ((2 * v.im : ℤ) : GaussianInt) := by
    have heq : ((2 * v.im : ℤ) : GaussianInt) =
        (⟨0, -1⟩ : GaussianInt) * (v - star v) := by
      ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]
      ring
    rw [heq]
    exact dvd_mul_of_dvd_right (dvd_sub h1 hs) _
  have hp' : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have hp2 : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have hn : p ∣ 2 := by exact_mod_cast h
    have hh := (Nat.dvd_prime Nat.prime_two).mp hn
    exact hh.elim hp.ne_one hpodd
  have hr : (p : ℤ) ∣ v.re :=
    (hp'.dvd_mul.mp ((factor_dvd_integer_iff hp hπ _).mp hreal)).resolve_left hp2
  have hi : (p : ℤ) ∣ v.im :=
    (hp'.dvd_mul.mp ((factor_dvd_integer_iff hp hπ _).mp himag)).resolve_left hp2
  exact hp'.not_isUnit (hv.isUnit_of_dvd' hr hi)

def signedFactor (π : GaussianInt) (b : Bool) : GaussianInt := if b then π else star π

theorem signedFactor_norm (π : GaussianInt) (b : Bool) : (signedFactor π b).norm = π.norm := by
  cases b <;> simp [signedFactor, Zsqrtd.norm_conj]

theorem signedFactor_irreducible {π : GaussianInt} (hπ : Irreducible π) (b : Bool) :
    Irreducible (signedFactor π b) := by
  cases b
  · exact (MulEquiv.irreducible_iff (starRingAut : RingAut GaussianInt)).mpr hπ
  · exact hπ

theorem coprime_factors_of_norm_primes {p q : ℕ} {π ρ : GaussianInt}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hπ : π.norm = (p : ℤ)) (hρ : ρ.norm = (q : ℤ)) : IsCoprime π ρ := by
  have hc : Nat.Coprime p q := (hp.coprime_iff_not_dvd).mpr (by
    intro hd
    have hh := (Nat.dvd_prime hq).mp hd
    exact hh.elim hp.ne_one hpq)
  have hcz : IsCoprime (p : ℤ) (q : ℤ) := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    simpa using hc
  have hcg := hcz.map (Int.castRingHom GaussianInt)
  have hdπ : π ∣ (p : GaussianInt) := (factor_dvd_integer_iff hp hπ _).mpr (dvd_refl _)
  have hdρ : ρ ∣ (q : GaussianInt) := (factor_dvd_integer_iff hq hρ _).mpr (dvd_refl _)
  exact hcg.of_isCoprime_of_dvd_left hdπ |>.of_isCoprime_of_dvd_right hdρ

theorem norm_finset_prod {ι : Type uIota} (s : Finset ι) (f : ι → GaussianInt) :
    (∏ i ∈ s, f i).norm = ∏ i ∈ s, (f i).norm := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, Zsqrtd.norm_mul, ih]

theorem SplitSieve.prod_factors_dvd (s : SplitSieve) (t : Finset ℕ) (ht : t ⊆ s.primes)
    (σ : ℕ → Bool) {v : GaussianInt}
    (hd : ∀ p ∈ t, signedFactor (s.factor p) (σ p) ∣ v) :
    (∏ p ∈ t, signedFactor (s.factor p) (σ p)) ∣ v := by
  apply Finset.prod_dvd_of_coprime _ hd
  intro p hp q hq hpq
  exact coprime_factors_of_norm_primes (s.prime_mem p (ht hp)) (s.prime_mem q (ht hq)) hpq
    ((signedFactor_norm _ _).trans (s.factor_norm p (ht hp)))
    ((signedFactor_norm _ _).trans (s.factor_norm q (ht hq)))

theorem SplitSieve.eligible_product_le_norm (s : SplitSieve) (t : Finset ℕ)
    (ht : t ⊆ s.primes) (σ : ℕ → Bool) {v : GaussianInt} (hv : v ≠ 0)
    (hd : ∀ p ∈ t, signedFactor (s.factor p) (σ p) ∣ v) :
    (∏ p ∈ t, (p : ℤ)) ≤ v.norm := by
  have hle := norm_le_of_dvd hv (s.prod_factors_dvd t ht σ hd)
  rw [norm_finset_prod] at hle
  convert hle using 1
  apply Finset.prod_congr rfl
  intro p hp
  exact ((signedFactor_norm _ _).trans (s.factor_norm p (ht hp))).symm

open scoped Classical in

theorem SplitSieve.uneligible_product_dvd_coefficient (s : SplitSieve)
    (t : Finset ℕ) (ht : t ⊆ s.primes) (σ : ℕ → Bool) (v : GaussianInt) (a : ℤ)
    (hw : (∏ p ∈ t, signedFactor (s.factor p) (σ p)) ∣ (a : GaussianInt) * v) :
    (∏ p ∈ t.filter (fun p => ¬ signedFactor (s.factor p) (σ p) ∣ v), (p : ℤ)) ∣ a := by
  classical
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq hpq
    have hp' := s.prime_mem p (ht (Finset.mem_filter.mp hp).1)
    have hq' := s.prime_mem q (ht (Finset.mem_filter.mp hq).1)
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    change Nat.Coprime p q
    exact (hp'.coprime_iff_not_dvd).mpr (fun h =>
      ((Nat.dvd_prime hq').mp h).elim hp'.ne_one hpq)
  · intro p hp
    obtain ⟨hpt, hpv⟩ := Finset.mem_filter.mp hp
    have hpp := ht hpt
    have hd : signedFactor (s.factor p) (σ p) ∣ (a : GaussianInt) * v :=
      (Finset.dvd_prod_of_mem _ hpt).trans hw
    have ha := ((signedFactor_irreducible (s.factor_irreducible p hpp) (σ p)).prime.dvd_mul.mp hd).resolve_right hpv
    exact (factor_dvd_integer_iff (s.prime_mem p hpp)
      ((signedFactor_norm _ _).trans (s.factor_norm p hpp)) a).mp ha

open scoped Classical in

theorem SplitSieve.line_witness_norm_lower (s : SplitSieve)
    (t : Finset ℕ) (ht : t ⊆ s.primes) (σ : ℕ → Bool)
    {v w : GaussianInt} (hv : PrimitiveDirection v) (hw : w ≠ 0)
    (hline : determinant v w = 0)
    (hdiv : (∏ p ∈ t, signedFactor (s.factor p) (σ p)) ∣ w) :
    v.norm * (∏ p ∈ t.filter (fun p => ¬ signedFactor (s.factor p) (σ p) ∣ v), (p : ℤ)) ^ 2
      ≤ w.norm := by
  classical
  obtain ⟨a, rfl⟩ := int_multiple_of_determinant_zero hv hline
  have ha : a ≠ 0 := by intro h; simp [h] at hw
  have hd := s.uneligible_product_dvd_coefficient t ht σ v a hdiv
  have habs : 0 < |a| := abs_pos.mpr ha
  have hle := Int.le_of_dvd habs ((dvd_abs _ _).mpr hd)
  have hprod : 0 ≤ ∏ p ∈ t.filter (fun p => ¬ signedFactor (s.factor p) (σ p) ∣ v), (p : ℤ) :=
    Finset.prod_nonneg (fun _ _ => Int.natCast_nonneg _)
  have hs : (∏ p ∈ t.filter (fun p => ¬ signedFactor (s.factor p) (σ p) ∣ v), (p : ℤ)) ^ 2 ≤ a ^ 2 := by
    nlinarith [sq_abs a]
  rw [Zsqrtd.norm_mul, Zsqrtd.norm_intCast]
  nlinarith [mul_le_mul_of_nonneg_left hs (GaussianInt.norm_nonneg v)]

end GaussianMoat

end OAI
