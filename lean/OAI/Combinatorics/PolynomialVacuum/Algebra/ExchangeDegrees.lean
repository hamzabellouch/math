import OAI.Combinatorics.PolynomialVacuum.Algebra.Triangularity

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

section Degrees
variable {ι : Type*} {i : ι} {p r : MvPolynomial ι ℂ} {a b : ℕ}

theorem dadd (hp : p.degreeOf i ≤ a) (hr : r.degreeOf i ≤ a) :
    (p+r).degreeOf i ≤ a := (degreeOf_add_le _ _ _).trans (max_le hp hr)

theorem dmul (hp : p.degreeOf i ≤ a) (hr : r.degreeOf i ≤ b) :
    (p*r).degreeOf i ≤ a+b := (degreeOf_mul_le _ _ _).trans (Nat.add_le_add hp hr)

theorem dpow (hp : p.degreeOf i ≤ a) (k : ℕ) :
    (p^k).degreeOf i ≤ k*a := (degreeOf_pow_le _ _ _).trans (Nat.mul_le_mul_left _ hp)

theorem dconst_mul (c : ℂ) (hp : p.degreeOf i ≤ a) :
    (C c*p).degreeOf i ≤ a := (degreeOf_C_mul_le _ _ _).trans hp

theorem dmul_const (c : ℂ) (hp : p.degreeOf i ≤ a) :
    (p*C c).degreeOf i ≤ a := (degreeOf_mul_C_le _ _ _).trans hp

end Degrees

theorem polyExchange_degree {ι : Type*} (x y : MvPolynomial ι ℂ) (a b : Pair)
    (i : ι) (d : ℕ) (hx : x.degreeOf i ≤ d) (hy : y.degreeOf i ≤ d) :
    (polyExchangeNumerator x y a b).degreeOf i ≤ 2*d := by
  rw [polyExchange_split]
  apply dadd
  · apply dadd
    · exact dmul_const _ (dpow hx 2)
    · simpa only [two_mul] using dmul_const (middleExchange a b) (dmul hx hy)
  · exact dmul_const _ (dpow hy 2)

theorem polyExchange_carried_loss {ι : Type*} (x y : MvPolynomial ι ℂ) (a b : Pair)
    (i : ι) (hx : x.degreeOf i ≤ 1) (hy : y.degreeOf i=0)
    (h : charge b.1 < charge a.2) : (polyExchangeNumerator x y a b).degreeOf i ≤ 1 := by
  rw [polyExchange_split,exchange_top_carried a b h,map_zero,mul_zero,zero_add]
  apply dadd
  · simpa using dmul_const (middleExchange a b) (dmul hx (le_of_eq hy))
  · exact (dmul_const _ (dpow (le_of_eq hy) 2)).trans (by norm_num)

theorem polyExchange_spectator_loss {ι : Type*} (x y : MvPolynomial ι ℂ) (a b : Pair)
    (i : ι) (hx : x.degreeOf i=0) (hy : y.degreeOf i ≤ 1)
    (h : charge b.2 < charge a.1) : (polyExchangeNumerator x y a b).degreeOf i ≤ 1 := by
  rw [polyExchange_split,exchange_top_spectator a b h,map_zero,mul_zero,add_zero]
  apply dadd
  · exact (dmul_const _ (dpow (le_of_eq hx) 2)).trans (by norm_num)
  · simpa using dmul_const (middleExchange a b) (dmul (le_of_eq hx) hy)

theorem degreeOf_rename_missing {ι κ : Type*} (f : ι → κ) (p : MvPolynomial ι ℂ)
    (j : κ) (h : ∀ i, f i≠j) : (rename f p).degreeOf j=0 := by
  by_contra hn
  obtain ⟨i,hi,he⟩ := mem_vars_rename f p (mem_vars_iff_degreeOf_ne_zero.mpr hn)
  exact h i he

theorem tensorExchange_degree {N : ℕ} {ι : Type*} (i j : Fin N)
    (x y : MvPolynomial ι ℂ) (W : PolynomialTensor N ι)
    (v : ι) (d k : ℕ) (hx : x.degreeOf v ≤ k) (hy : y.degreeOf v ≤ k)
    (hW : ∀ s, (W s).degreeOf v ≤ d) (s : Fin N → Spin) :
    (tensorExchange i j x y W s).degreeOf v ≤ d+2*k := by
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro ab _
  exact (dmul (polyExchange_degree x y (s i,s j) ab v k hx hy) (hW _)).trans (by omega)

end PolynomialVacuumAlgebra

end OAI
