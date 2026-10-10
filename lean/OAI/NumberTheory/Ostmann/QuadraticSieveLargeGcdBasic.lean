import OAI.NumberTheory.Ostmann.QuadraticSieveGcdSeparationBound

namespace OAI

namespace Ostmann.QuadraticSieve

noncomputable def gcdCorrelation (S : Finset ℕ) (F : ℕ → ℂ) (d : ℕ) : ℂ :=
  ∑ n ∈ S, ∑ t ∈ S, if n.gcd t = d then F n * star (F t) else 0

theorem gcdCorrelation_eq_quotient (S : Finset ℕ) (F : ℕ → ℂ)
    {d : ℕ} (hd : 0 < d) :
    gcdCorrelation S F d =
      ∑ r ∈ quotientSupport S d, ∑ s ∈ quotientSupport S d,
        if r.Coprime s then F (d * r) * star (F (d * s)) else 0 := by
  have hmul (r s : ℕ) : (d * r).gcd (d * s) = d ↔ r.Coprime s := by
    rw [Nat.gcd_mul_left, Nat.Coprime]
    constructor
    · intro he
      have he' : d * r.gcd s = d * 1 := by simpa only [mul_one] using he
      exact mul_left_cancel₀ hd.ne' he'
    · intro he
      rw [he, mul_one]
  symm
  calc
    _ = ∑ r ∈ quotientSupport S d, ∑ s ∈ quotientSupport S d,
        if (d * r).gcd (d * s) = d then F (d * r) * star (F (d * s)) else 0 := by
      simp only [hmul]
    _ = ∑ r ∈ quotientSupport S d, ∑ t ∈ S,
        if d ∣ t then (if (d * r).gcd t = d then F (d * r) * star (F t) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      exact sum_quotientSupport S d
        (fun t => if (d * r).gcd t = d then F (d * r) * star (F t) else 0)
    _ = ∑ n ∈ S, if d ∣ n then
        (∑ t ∈ S, if d ∣ t then (if n.gcd t = d then F n * star (F t) else 0) else 0) else 0 :=
      sum_quotientSupport S d
        (fun n => ∑ t ∈ S, if d ∣ t then (if n.gcd t = d then F n * star (F t) else 0) else 0)
    _ = _ := by
      unfold gcdCorrelation
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hdn : d ∣ n
      · rw [ite_eq_left hdn]
        apply Finset.sum_congr rfl
        intro t ht
        by_cases hdt : d ∣ t
        · simp only [ite_eq_left hdt]
        · have hne : n.gcd t ≠ d := fun h => hdt (h ▸ Nat.gcd_dvd_right n t)
          simp only [ite_eq_right hdt, ite_eq_right hne]
      · have hne (t : ℕ) : n.gcd t ≠ d := fun h => hdn (h ▸ Nat.gcd_dvd_left n t)
        simp only [ite_eq_right hdn, ite_eq_right (hne _), Finset.sum_const_zero]

theorem sum_gcdCorrelation (S : Finset ℕ) (F : ℕ → ℂ) (N : ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    (∑ d ∈ Finset.Icc 1 N, gcdCorrelation S F d) =
      (∑ n ∈ S, F n) * star (∑ n ∈ S, F n) := by
  unfold gcdCorrelation
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.Icc 1 N) (t := S)]
  have hmem (n : ℕ) (hn : n ∈ S) (t : ℕ) : n.gcd t ∈ Finset.Icc 1 N :=
    Finset.mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_left t (hS n hn).1,
      (Nat.gcd_le_left t (hS n hn).1).trans (hS n hn).2⟩
  calc
    _ = ∑ n ∈ S, ∑ t ∈ S, F n * star (F t) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro t ht
      simp [hmem n hn t]
    _ = _ := by rw [star_sum, Finset.sum_mul]; simp only [Finset.mul_sum]

theorem norm_sum_sq_le_sum_norm_gcdCorrelation (S : Finset ℕ) (F : ℕ → ℂ) (N : ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    ‖∑ n ∈ S, F n‖ ^ 2 ≤ ∑ d ∈ Finset.Icc 1 N, ‖gcdCorrelation S F d‖ := by
  have h := norm_sum_le (Finset.Icc 1 N) (gcdCorrelation S F)
  rw [sum_gcdCorrelation S F N hS, norm_mul, norm_star, ← pow_two] at h
  exact h

theorem coprime_correlation_norm_le (S : Finset ℕ) (F : ℕ → ℂ) (N : ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    ‖∑ n ∈ S, ∑ t ∈ S, if n.Coprime t then F n * star (F t) else 0‖ ≤
      ∑ k ∈ Finset.Icc 1 N, ‖∑ n ∈ S, if k ∣ n then F n else 0‖ ^ 2 := by
  have h := coprime_bilinear_norm_le S S F (fun t => star (F t)) N hS
  apply h.trans_eq
  apply Finset.sum_congr rfl
  intro k hk
  have he : (∑ t ∈ S, if k ∣ t then star (F t) else 0) =
      star (∑ t ∈ S, if k ∣ t then F t else 0) := by
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro t ht
    split <;> simp
  rw [he, norm_star, pow_two]

noncomputable def gcdJacobiRow (S : Finset ℕ) (a : ℕ → ℂ) (d : ℕ) (m : ℤ) : ℂ :=
  gcdCorrelation S (fun n => a n * (jacobiSym m n : ℂ)) d

theorem gcdJacobiRow_eq_denominator (S : Finset ℕ) (a : ℕ → ℂ) (d : ℕ) (m : ℤ)
    (hS : ∀ n ∈ S, 0 < n) :
    gcdJacobiRow S a d m = ∑ n ∈ S, ∑ t ∈ S,
      if n.gcd t = d then a n * star (a t) * (jacobiSym m (n * t) : ℂ) else 0 := by
  unfold gcdJacobiRow gcdCorrelation
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro t ht
  rw [jacobiSym.mul_right' m (hS n hn).ne' (hS t ht).ne']
  simp only [Int.cast_mul, star_mul, star_intCast]
  split <;> ring

theorem gcdJacobiRow_norm_le_quotient (S : Finset ℕ) (a : ℕ → ℂ)
    {d : ℕ} (hd : 0 < d) (hS : ∀ n ∈ S, 0 < n) (m : ℤ) :
    ‖gcdJacobiRow S a d m‖ ≤
      ‖∑ r ∈ quotientSupport S d, ∑ s ∈ quotientSupport S d,
        if r.Coprime s then (a (d * r) * (jacobiSym m r : ℂ)) *
          star (a (d * s) * (jacobiSym m s : ℂ)) else 0‖ := by
  unfold gcdJacobiRow
  rw [gcdCorrelation_eq_quotient S _ hd]
  have he : (∑ r ∈ quotientSupport S d, ∑ s ∈ quotientSupport S d,
      if r.Coprime s then (a (d * r) * (jacobiSym m (d * r) : ℂ)) *
        star (a (d * s) * (jacobiSym m (d * s) : ℂ)) else 0) =
      (jacobiSym m d : ℂ) ^ 2 *
        (∑ r ∈ quotientSupport S d, ∑ s ∈ quotientSupport S d,
          if r.Coprime s then (a (d * r) * (jacobiSym m r : ℂ)) *
            star (a (d * s) * (jacobiSym m s : ℂ)) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [jacobiSym.mul_right' m hd.ne' (quotientSupport_pos hS hr).ne',
      jacobiSym.mul_right' m hd.ne' (quotientSupport_pos hS hs).ne']
    simp only [Int.cast_mul, star_mul, star_intCast]
    split <;> ring
  rw [he]
  rcases jacobiSym.trichotomy m d with h | h | h <;> simp [h]

end Ostmann.QuadraticSieve

end OAI
