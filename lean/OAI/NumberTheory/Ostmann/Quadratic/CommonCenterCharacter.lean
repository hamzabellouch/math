import OAI.NumberTheory.Ostmann.Construction.OriginalTailCenter
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticKernelBias

namespace OAI

/-! # Translating the original local biases to the common affine form -/

namespace Ostmann

open scoped BigOperators

theorem jacobi_commonCenter_identity (m p : ℕ) (h x t : ℤ) [Fact p.Prime]
    (hmp : m < p) (hm : 0 < m)
    (ht : (t : ZMod p) = (h : ZMod p) / (m : ZMod p)) :
    jacobiSym (x - t) p = jacobiSym (m : ℤ) p * jacobiSym ((m : ℤ) * x - h) p := by
  have hm0 : (m : ZMod p) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff m p).not.mpr (Nat.not_dvd_of_pos_of_lt hm hmp)
  have htm : (m : ZMod p) * (t : ZMod p) = (h : ZMod p) := by
    rw [ht]
    field_simp
  have hmod : (((m : ℤ) * (x - t) : ℤ) : ZMod p) = (((m : ℤ) * x - h : ℤ) : ZMod p) := by
    push_cast
    linear_combination -htm
  have hχ := jacobiSym.mod_left' ((ZMod.intCast_eq_intCast_iff' _ _ p).mp hmod)
  rw [jacobiSym.mul_left] at hχ
  have hcop : (m : ℤ).gcd p = 1 := by
    simpa using ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt hm hmp) : p.Coprime m).symm
  have hsq := jacobiSym.sq_one hcop
  calc
    _ = jacobiSym (m : ℤ) p ^ 2 * jacobiSym (x - t) p := by rw [hsq, one_mul]
    _ = _ := by rw [← hχ]; ring

noncomputable def commonCenterOrientation (ε : ℕ → ℝ) (m : ℕ) (p : ℕ) : ℂ :=
  (ε p : ℂ) * (jacobiSym (m : ℤ) p : ℂ)

theorem commonCenterOrientation_norm (ε : ℕ → ℝ) (m p : ℕ)
    (hε : ε p = 1 ∨ ε p = -1) : ‖commonCenterOrientation ε m p‖ ≤ 1 := by
  unfold commonCenterOrientation
  rw [norm_mul]
  have he : ‖(ε p : ℂ)‖ = 1 := by rcases hε with h | h <;> simp [h]
  rw [he, one_mul]
  exact norm_jacobi_complex_le _ _

theorem commonCenter_oriented_value (ε : ℕ → ℝ) (t : ℕ → ℤ)
    (m p : ℕ) (h x : ℤ) [Fact p.Prime] (hmp : m < p) (hm : 0 < m)
    (ht : (t p : ZMod p) = (h : ZMod p) / (m : ZMod p)) :
    (orientedQuadraticValue ε t x p : ℂ) =
      commonCenterOrientation ε m p * (jacobiSym ((m : ℤ) * x - h) p : ℂ) := by
  unfold orientedQuadraticValue commonCenterOrientation
  push_cast
  rw [jacobi_commonCenter_identity m p h x (t p) hmp hm ht]
  push_cast
  ring

theorem quadraticPrimeMean_commonCenter (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (ε : ℕ → ℝ) (t : ℕ → ℤ) (m : ℕ) (h x : ℤ) (hm : 0 < m)
    (hmp : ∀ p ∈ P, m < p)
    (ht : ∀ (p : ℕ) (hp : p ∈ P),
      let _ : Fact p.Prime := ⟨hP p hp⟩
      (t p : ZMod p) = (h : ZMod p) / (m : ZMod p)) :
    quadraticPrimeMean P (commonCenterOrientation ε m) ((m : ℤ) * x - h) =
      (((∑ p ∈ P, orientedQuadraticValue ε t x p) / P.card : ℝ) : ℂ) := by
  unfold quadraticPrimeMean
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  let : Fact p.Prime := ⟨hP p hp⟩
  exact (commonCenter_oriented_value ε t m p h x (hmp p hp) hm (ht p hp)).symm

end Ostmann

end OAI
