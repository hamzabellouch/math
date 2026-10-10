import Mathlib

namespace OAI


namespace Problem355.ShortRelations

open scoped BigOperators

theorem intCast_ne_zero_of_abs_lt {q : ℕ} {x : ℤ}
    (hx : x ≠ 0) (hbound : |x| < (q : ℤ)) : (x : ZMod q) ≠ 0 := by
  intro hcast
  exact hx (Int.eq_zero_of_abs_lt_dvd
    ((ZMod.intCast_zmod_eq_zero_iff_dvd x q).1 hcast) hbound)

theorem sum_smul_ne_zero_of_sum_eq_zero
    {ι V : Type*} [Fintype ι] {q : ℕ}
    [AddCommGroup V] [Module (ZMod q) V]
    {p : ι → V} (hp : AffineIndependent (ZMod q) p)
    {x : ι → ℤ} (hsum : ∑ i, x i = 0)
    (hshort : ∀ i, |x i| < (q : ℤ)) (hne : x ≠ 0) :
    (∑ i, (x i : ZMod q) • p i) ≠ 0 := by
  classical
  intro hrel
  have hsum' : ∑ i, (x i : ZMod q) = 0 := by
    simpa only [Int.cast_sum, Int.cast_zero] using
      congrArg (fun z : ℤ => (z : ZMod q)) hsum
  have hz : ∀ i, (x i : ZMod q) = 0 := by
    intro i
    exact hp.eq_zero_of_sum_eq_zero hsum' hrel i (Finset.mem_univ i)
  apply hne
  funext i
  exact Int.eq_zero_of_abs_lt_dvd
    ((ZMod.intCast_zmod_eq_zero_iff_dvd (x i) q).1 (hz i)) (hshort i)

theorem sum_smul_ne_zero_of_bounded_coefficients
    {ι V : Type*} [Fintype ι] {q H : ℕ}
    [AddCommGroup V] [Module (ZMod q) V]
    {p : ι → V} (hp : AffineIndependent (ZMod q) p)
    {x : ι → ℤ} (hsum : ∑ i, x i = 0)
    (hshort : ∀ i, |x i| ≤ (H : ℤ)) (hHq : H < q) (hne : x ≠ 0) :
    (∑ i, (x i : ZMod q) • p i) ≠ 0 := by
  apply sum_smul_ne_zero_of_sum_eq_zero hp hsum ?_ hne
  intro i
  exact lt_of_le_of_lt (hshort i) (by exact_mod_cast hHq)

theorem mulVec_ne_zero_of_sum_eq_zero
    {m ι : Type*} [Fintype ι] {q : ℕ}
    {A : Matrix m ι (ZMod q)}
    (hA : AffineIndependent (ZMod q) (fun j => fun i => A i j))
    {x : ι → ℤ} (hsum : ∑ j, x j = 0)
    (hshort : ∀ j, |x j| < (q : ℤ)) (hne : x ≠ 0) :
    A.mulVec (fun j => (x j : ZMod q)) ≠ 0 := by
  have h := sum_smul_ne_zero_of_sum_eq_zero hA hsum hshort hne
  convert h using 1
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

end Problem355.ShortRelations

end OAI
