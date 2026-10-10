import OAI.NumberTheory.Ostmann.QuadraticCenter.InverseWeylPhase
import OAI.NumberTheory.Ostmann.QuadraticCenter.WeightedPoisson

namespace OAI

namespace Ostmann.QuadraticCenter

theorem stdAddChar_eq_weylPhase {q : ℕ} [NeZero q] (a : ℤ) :
    ZMod.stdAddChar (a : ZMod q) = weylPhase ((a : ℝ) / q) := by
  rw [ZMod.stdAddChar_coe, weylPhase, Real.fourierChar_apply]
  push_cast
  congr 1
  ring

theorem weylPhase_eq_of_sub_int {x y : ℝ} (k : ℤ) (h : x - y = k) :
    weylPhase x = weylPhase y := by
  have he : x = y + k := by linarith
  rw [he, weylPhase_add, weylPhase_int, mul_one]

theorem bezout_center_divisibility {q d : ℕ} (r s t h : ℤ)
    (hbez : (d : ℤ) * r + (q : ℤ) * s = 1)
    (hc : (d : ℤ) ∣ t + (q : ℤ) * h) : (d : ℤ) ∣ s * t + h := by
  obtain ⟨a, ha⟩ := hc
  refine ⟨s * a + r * h, ?_⟩
  linear_combination s * ha - h * hbez

theorem stdAddChar_common_center {q d : ℕ} [NeZero q] [NeZero d]
    (r s t h u : ℤ) (hbez : (d : ℤ) * r + (q : ℤ) * s = 1)
    (hc : (d : ℤ) ∣ t + (q : ℤ) * h) :
    ZMod.stdAddChar (((u * r : ℤ) : ZMod q) * (t : ZMod q)) =
      weylPhase (((t : ℝ) / q + h) * u / d) := by
  rw [← Int.cast_mul, stdAddChar_eq_weylPhase]
  obtain ⟨b, hb⟩ := bezout_center_divisibility r s t h hbez hc
  apply weylPhase_eq_of_sub_int (-(u * b))
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hz : (d : ℝ) * r + (q : ℝ) * s = 1 := by exact_mod_cast hbez
  have hbR : (s : ℝ) * t + h = (d : ℝ) * b := by exact_mod_cast hb
  push_cast
  field_simp
  linear_combination (u : ℝ) * (t : ℝ) * hz - (u : ℝ) * (q : ℝ) * hbR

theorem jacobi_bezout_inverse {q d : ℕ} [NeZero q]
    (r s : ℤ) (hbez : (d : ℤ) * r + (q : ℤ) * s = 1) :
    jacobiSym r q = jacobiSym (d : ℤ) q := by
  have hmod : (((d : ℤ) * r : ℤ) : ZMod q) = 1 := by
    have he := congrArg (fun a : ℤ => (a : ZMod q)) hbez
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      zero_mul, add_zero, Int.cast_one] using he
  have hJ : jacobiSym ((d : ℤ) * r) q = 1 := by
    rw [← jacobiSym.one_left q]
    apply jacobiSym.mod_left'
    exact (ZMod.intCast_eq_intCast_iff' _ _ q).mp (by simpa only [Int.cast_one] using hmod)
  rw [jacobiSym.mul_left] at hJ
  rcases jacobiSym.trichotomy (d : ℤ) q with hd | hd | hd <;> rw [hd] at hJ ⊢ <;> omega

theorem jacobi_mul_bezout_inverse {q d : ℕ} [NeZero q]
    (r s u : ℤ) (hbez : (d : ℤ) * r + (q : ℤ) * s = 1) :
    jacobiSym (u * r) q = jacobiSym u q * jacobiSym (d : ℤ) q := by
  rw [jacobiSym.mul_left, jacobi_bezout_inverse r s hbez]

end Ostmann.QuadraticCenter

end OAI
