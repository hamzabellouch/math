import Mathlib

namespace OAI


namespace Problem355.PrimitiveVector

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem exists_factorization (x : ι → ℤ) (hx : x ≠ 0) :
    ∃ (g : ℤ) (y z : ι → ℤ),
      0 < g ∧ (∀ i, x i = g * y i) ∧ (∑ i, y i * z i = 1) ∧
      (∀ i, |y i| ≤ |x i|) ∧ (∀ i, y i = 0 ↔ x i = 0) := by
  classical
  have hxi : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hx (funext h)
  obtain ⟨i, hi⟩ := hxi
  let g : ℤ := Finset.univ.gcd x
  have hg_nonneg : 0 ≤ g :=
    Int.nonneg_of_normalize_eq_self (Finset.normalize_gcd)
  have hg_ne : g ≠ 0 := by
    intro hg
    exact hi ((Finset.gcd_eq_zero_iff.mp hg) i (Finset.mem_univ i))
  have hg_pos : 0 < g := lt_of_le_of_ne hg_nonneg (Ne.symm hg_ne)
  obtain ⟨y, hxy, hy⟩ := Finset.extract_gcd x
    (show (Finset.univ : Finset ι).Nonempty from ⟨i, Finset.mem_univ i⟩)
  have hfactor : ∀ i, x i = g * y i := fun i => hxy i (Finset.mem_univ i)
  obtain ⟨z, hz⟩ := Finset.gcd_eq_sum_mul (Finset.univ : Finset ι) y
  have hbezout : ∑ i, y i * z i = 1 := by
    simpa only [hy] using hz.symm
  refine ⟨g, y, z, hg_pos, hfactor, hbezout, ?_, ?_⟩
  · intro j
    rw [hfactor j, abs_mul, abs_of_pos hg_pos]
    have hg_one : 1 ≤ g := hg_pos
    nlinarith [abs_nonneg (y j)]
  · intro j
    rw [hfactor j]
    simp [hg_ne]

theorem dot_eq_zero_of_factor {g : ℤ} (hg : g ≠ 0)
    {x y : ι → ℤ} (hxy : ∀ i, x i = g * y i)
    (a : ι → ℤ) (ha : ∑ i, a i * x i = 0) :
    ∑ i, a i * y i = 0 := by
  have hmul : g * (∑ i, a i * y i) = 0 := by
    calc
      _ = ∑ i, a i * x i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hxy i]
        ring
      _ = 0 := ha
  exact (mul_eq_zero.mp hmul).resolve_left hg

theorem exists_factorization_mem_ker {κ : Type*}
    (A : Matrix κ ι ℤ) (x : ι → ℤ) (hx : x ≠ 0)
    (hAx : A.mulVec x = 0) :
    ∃ (g : ℤ) (y z : ι → ℤ),
      0 < g ∧ (∀ i, x i = g * y i) ∧ (∑ i, y i * z i = 1) ∧
      (∀ i, |y i| ≤ |x i|) ∧ (∀ i, y i = 0 ↔ x i = 0) ∧
      A.mulVec y = 0 := by
  obtain ⟨g, y, z, hg, hxy, hyz, hbound, hzero⟩ := exists_factorization x hx
  refine ⟨g, y, z, hg, hxy, hyz, hbound, hzero, ?_⟩
  funext k
  apply dot_eq_zero_of_factor hg.ne' hxy (A k)
  exact congrFun hAx k

end Problem355.PrimitiveVector

end OAI
