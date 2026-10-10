import OAI.NumberTheory.JointDickman.Arithmetic.AdditionSieveGeometry

namespace OAI

/-! # The negative-slope progression for a large low-endpoint addition -/

namespace JointDickman
open Finset Classical

theorem low_addition_equation_modEq {e j b z w c d : ℕ} (hej : e.Coprime j)
    (hz : e*z+j*c = b) (hw : e*w+j*d = b) : Nat.ModEq j z w := by
  have hez : (e*z)%j = b%j := by simpa [Nat.add_mod] using congrArg (fun n => n%j) hz
  have hew : (e*w)%j = b%j := by simpa [Nat.add_mod] using congrArg (fun n => n%j) hw
  exact Nat.ModEq.cancel_left_of_coprime hej.symm (hez.trans hew.symm)

theorem low_addition_equation_progression {e j b w d : ℕ} (hj : 0 < j) (hej : e.Coprime j)
    (hw : e*w+j*d = b) :
    ∃ (z₀ : ℕ) (c₀ : ℤ), z₀ < j ∧
      (e : ℤ)*z₀+(j : ℤ)*c₀ = b ∧
      ∀ (z c : ℕ), e*z+j*c = b →
        z = z₀+j*(z/j) ∧ (c : ℤ) = c₀-(e : ℤ)*((z/j : ℕ) : ℤ) := by
  let z₀ := w%j
  let c₀ : ℤ := (d : ℤ)+(e : ℤ)*((w/j : ℕ) : ℤ)
  have hwdecomp : w = z₀+j*(w/j) := (Nat.mod_add_div w j).symm
  have hwInt : (e : ℤ)*w+(j : ℤ)*d = b := by exact_mod_cast hw
  have hwdecInt : (w : ℤ) = z₀+(j : ℤ)*((w/j : ℕ) : ℤ) := by exact_mod_cast hwdecomp
  have hbase : (e : ℤ)*z₀+(j : ℤ)*c₀ = b := by
    dsimp only [c₀]
    simp only [Int.natCast_ediv] at hwdecInt ⊢
    linear_combination hwInt-(e : ℤ)*hwdecInt
  refine ⟨z₀,c₀,Nat.mod_lt _ hj,hbase,?_⟩
  intro z c hz
  have hmod : z%j = w%j := low_addition_equation_modEq hej hz hw
  have hzdec : z = z₀+j*(z/j) := by
    change z = w%j+j*(z/j)
    rw [← hmod]
    exact (Nat.mod_add_div z j).symm
  refine ⟨hzdec,?_⟩
  have hzInt : (e : ℤ)*z+(j : ℤ)*c = b := by exact_mod_cast hz
  have hzdecInt : (z : ℤ) = z₀+(j : ℤ)*((z/j : ℕ) : ℤ) := by exact_mod_cast hzdec
  apply mul_left_cancel₀ (show (j : ℤ) ≠ 0 by exact_mod_cast hj.ne')
  simp only [Int.natCast_ediv] at hzdecInt ⊢
  linear_combination hzInt-hbase-(e : ℤ)*hzdecInt

theorem low_addition_progression_good_primes {B e j b z₀ : ℕ} {g : ℝ}
    (he : 0 < e) (hb : 0 < b) (hj : 0 < j) (hcut : j ≤ auxiliaryCutoff B)
    {c : ℤ} (hbase : (e : ℤ)*z₀+(j : ℤ)*c = b) :
    ∀ p ∈ primePrefix B g (auxiliaryPrimes B) \ additionExcludedPrimes B e b,
      (j : ZMod p) ≠ 0 ∧ (-(e : ℤ) : ZMod p) ≠ 0 ∧
        (z₀ : ZMod p)*(-(e : ℤ) : ZMod p)-(c : ZMod p)*j ≠ 0 := by
  have hbase' : (e : ℤ)*z₀ = b+(j : ℤ)*(-c) := by linarith
  intro p hp
  obtain ⟨hj,he,hd⟩ := addition_progression_good_primes he hb hj hcut hbase' p hp
  refine ⟨hj,?_,?_⟩
  · simpa only [Int.cast_neg,Int.cast_natCast,neg_ne_zero] using he
  · have hid : (z₀ : ZMod p)*(-(e : ℤ) : ZMod p)-(c : ZMod p)*j =
        -((z₀ : ZMod p)*e-((-c : ℤ) : ZMod p)*j) := by
      simp only [Int.cast_neg,Int.cast_natCast]
      ring
    rw [hid]
    exact neg_ne_zero.mpr hd

end JointDickman

end OAI
