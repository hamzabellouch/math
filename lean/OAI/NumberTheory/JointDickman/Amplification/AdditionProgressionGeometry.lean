import OAI.NumberTheory.JointDickman.Arithmetic.NumericPrefixHarmonic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.GCD.BigOperators

namespace OAI

/-! # The actual progression of numeric additions -/

namespace JointDickman
open Finset Classical

/-- Every selected coefficient is a unit modulo an allowed lag. -/
theorem auxiliary_product_coprime_lag {B j : ℕ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hj : 0 < j) (hcut : j ≤ auxiliaryCutoff B) :
    (∏ p ∈ A, p : ℕ).Coprime j := by
  apply Nat.coprime_prod_left_iff.mpr
  intro p hp
  have hprime := auxiliaryPrimes_prime B p (hA hp)
  have hbig : auxiliaryCutoff B < p := by exact_mod_cast (mem_filter.mp (hA hp)).2
  exact Nat.coprime_of_lt_prime hj.ne' (lt_of_le_of_lt hcut hbig) hprime

/-- Once the retained factors and the other addition are fixed, two valid
numeric additions have the same residue modulo the lag. -/
theorem addition_equation_modEq {e j b z w c d : ℕ} (hej : e.Coprime j)
    (hz : e*z = b+j*c) (hw : e*w = b+j*d) : Nat.ModEq j z w := by
  have he : Nat.ModEq j (e*z) (e*w) := by
    change (e*z)%j = (e*w)%j
    rw [hz,hw]
    simp [Nat.add_mod]
  exact Nat.ModEq.cancel_left_of_coprime hej.symm he

/-- A nonempty coefficient class has one residue z₀ and one integral
intercept c₀. Every other member is z=z₀+jt, c=c₀+et with t=z/j. -/
theorem addition_equation_progression {e j b w d : ℕ} (hj : 0 < j) (hej : e.Coprime j)
    (hw : e*w = b+j*d) :
    ∃ (z₀ : ℕ) (c₀ : ℤ), z₀ < j ∧
      (e : ℤ)*z₀ = b+(j : ℤ)*c₀ ∧
      ∀ (z c : ℕ), e*z = b+j*c →
        z = z₀+j*(z/j) ∧ (c : ℤ) = c₀+(e : ℤ)*((z/j : ℕ) : ℤ) := by
  let z₀ := w%j
  let c₀ : ℤ := (d : ℤ)-(e : ℤ)*((w/j : ℕ) : ℤ)
  have hwdecomp : w = z₀+j*(w/j) := (Nat.mod_add_div w j).symm
  have hwInt : (e : ℤ)*w = b+(j : ℤ)*d := by exact_mod_cast hw
  have hwdecInt : (w : ℤ) = z₀+(j : ℤ)*((w/j : ℕ) : ℤ) := by exact_mod_cast hwdecomp
  have hbase : (e : ℤ)*z₀ = b+(j : ℤ)*c₀ := by
    dsimp [c₀]
    simp only [Int.natCast_ediv] at hwdecInt
    linear_combination hwInt-(e : ℤ)*hwdecInt
  refine ⟨z₀,c₀,Nat.mod_lt _ hj,hbase,?_⟩
  intro z c hz
  have hmod : z%j = w%j := addition_equation_modEq hej hz hw
  have hzdec : z = z₀+j*(z/j) := by
    change z = w%j+j*(z/j)
    rw [← hmod]
    exact (Nat.mod_add_div z j).symm
  refine ⟨hzdec,?_⟩
  have hzInt : (e : ℤ)*z = b+(j : ℤ)*c := by exact_mod_cast hz
  have hzdecInt : (z : ℤ) = z₀+(j : ℤ)*((z/j : ℕ) : ℤ) := by exact_mod_cast hzdec
  apply mul_left_cancel₀ (show (j : ℤ) ≠ 0 by exact_mod_cast hj.ne')
  simp only [Int.natCast_ediv] at hzdecInt ⊢
  linear_combination -hzInt+hbase+(e : ℤ)*hzdecInt

/-- The determinant of the two progression forms is the fixed nonzero
opposite coefficient, with no dependence on the progression variable. -/
theorem addition_progression_determinant {e j b z₀ : ℕ} {c₀ : ℤ}
    (hbase : (e : ℤ)*z₀ = b+(j : ℤ)*c₀) :
    (z₀ : ℤ)*e-c₀*j = b := by linear_combination hbase

end JointDickman

end OAI
