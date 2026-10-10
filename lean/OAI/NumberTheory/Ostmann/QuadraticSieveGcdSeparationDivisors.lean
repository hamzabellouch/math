import OAI.NumberTheory.Ostmann.QuadraticSieveGcdSeparation

namespace OAI

namespace Ostmann.QuadraticSieve

open scoped ArithmeticFunction.Moebius

theorem coprime_divisor_pair_unique {n t d x y : ℕ} (hnt : n.Coprime t)
    (hxy : x * y = d) (hx : x ∣ n) (hy : y ∣ t) :
    x = d.gcd n ∧ y = d.gcd t := by
  have hyn : y.Coprime n := hnt.symm.of_dvd_left hy
  have hxt : x.Coprime t := hnt.of_dvd_left hx
  constructor
  · symm
    rw [← hxy, hyn.gcd_mul_right_cancel x, Nat.gcd_eq_left_iff_dvd.mpr hx]
  · symm
    rw [← hxy, hxt.gcd_mul_left_cancel y, Nat.gcd_eq_left_iff_dvd.mpr hy]

theorem coprime_divisor_pair_indicator {n t d : ℕ} (hnt : n.Coprime t)
    (hd : d ≠ 0) (z : ℂ) :
    (if d ∣ n * t then z else 0) =
      ∑ e ∈ d.divisorsAntidiagonal, if e.1 ∣ n ∧ e.2 ∣ t then z else 0 := by
  by_cases hdiv : d ∣ n * t
  · have hmul : d.gcd n * d.gcd t = d :=
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hnt).mpr hdiv
    have he : (d.gcd n, d.gcd t) ∈ d.divisorsAntidiagonal :=
      Nat.mem_divisorsAntidiagonal.mpr ⟨hmul, hd⟩
    rw [ite_eq_left hdiv]
    symm
    rw [Finset.sum_eq_single (d.gcd n, d.gcd t)]
    · simp only [Nat.gcd_dvd_right, and_self, ite_true]
    · intro e he' hne
      by_cases hediv : e.1 ∣ n ∧ e.2 ∣ t
      · have hpair := coprime_divisor_pair_unique hnt
          (Nat.mem_divisorsAntidiagonal.mp he').1 hediv.1 hediv.2
        exact (hne (Prod.ext hpair.1 hpair.2)).elim
      · exact ite_eq_right hediv
    · exact fun h => (h he).elim
  · rw [ite_eq_right hdiv]
    symm
    apply Finset.sum_eq_zero
    intro e he
    apply ite_eq_right
    intro hediv
    apply hdiv
    rw [← (Nat.mem_divisorsAntidiagonal.mp he).1]
    exact Nat.mul_dvd_mul hediv.1 hediv.2

theorem coprime_product_divisor_partition (S T : Finset ℕ) (F : ℕ → ℕ → ℂ)
    (d : ℕ) (hd : d ≠ 0) :
    (∑ n ∈ S, ∑ t ∈ T, if n.Coprime t ∧ d ∣ n * t then F n t else 0) =
      ∑ e ∈ d.divisorsAntidiagonal, ∑ n ∈ S, ∑ t ∈ T,
        if n.Coprime t ∧ e.1 ∣ n ∧ e.2 ∣ t then F n t else 0 := by
  calc
    _ = ∑ n ∈ S, ∑ t ∈ T, ∑ e ∈ d.divisorsAntidiagonal,
        if n.Coprime t ∧ e.1 ∣ n ∧ e.2 ∣ t then F n t else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hnt : n.Coprime t
      · simp_rw [ite_and, ite_eq_left hnt]
        simpa only [ite_and] using coprime_divisor_pair_indicator hnt hd (F n t)
      · simp [hnt]
    _ = ∑ n ∈ S, ∑ e ∈ d.divisorsAntidiagonal, ∑ t ∈ T,
        if n.Coprime t ∧ e.1 ∣ n ∧ e.2 ∣ t then F n t else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem coprime_product_jacobi_moebius (S T : Finset ℕ) (a b : ℕ → ℂ)
    (m : ℤ) (d N : ℕ) (hd : d ≠ 0)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) (hT : ∀ t ∈ T, 0 < t) :
    (∑ n ∈ S, ∑ t ∈ T,
      if n.Coprime t ∧ d ∣ n * t then a n * b t * (jacobiSym m (n * t) : ℂ) else 0) =
      ∑ e ∈ d.divisorsAntidiagonal, ∑ k ∈ Finset.Icc 1 N, (μ k : ℂ) *
        (∑ n ∈ S, if k ∣ n ∧ e.1 ∣ n then a n * (jacobiSym m n : ℂ) else 0) *
        (∑ t ∈ T, if k ∣ t ∧ e.2 ∣ t then b t * (jacobiSym m t : ℂ) else 0) := by
  rw [coprime_product_divisor_partition S T _ d hd]
  apply Finset.sum_congr rfl
  intro e he
  exact coprime_jacobi_bilinear_moebius S T a b m e.1 e.2 N hS hT

end Ostmann.QuadraticSieve

end OAI
