import Mathlib.Data.ZMod.QuotientRing
import OAI.NumberTheory.Ostmann.Supply.FiniteParseval

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators ComplexConjugate

def frequencyEmbedding {d q : ℕ} (x : ZMod d) : ZMod q :=
  (q / d : ℕ) * (x.val : ZMod q)

theorem stdAddChar_frequency_lift {d q : ℕ} [NeZero d] [NeZero q]
    (hdq : d ∣ q) (n : ℤ) :
    ZMod.stdAddChar (((q / d : ℕ) : ZMod q) * (n : ZMod q)) =
      ZMod.stdAddChar (n : ZMod d) := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hmul : ((q / d : ℕ) : ℂ) * d = q := by
    exact_mod_cast Nat.div_mul_cancel hdq
  have h := ZMod.stdAddChar_coe (N := q) (((q / d : ℕ) : ℤ) * n)
  simp only [Int.cast_mul, Int.cast_natCast] at h
  rw [h, ZMod.stdAddChar_coe]
  apply congrArg Complex.exp
  field_simp
  linear_combination (n : ℂ) * hmul

theorem stdAddChar_restrict_eq_lift {d q : ℕ} [NeZero d] [NeZero q]
    (hdq : d ∣ q) (x : ZMod d) (s : ZMod q) :
    ZMod.stdAddChar (x * ZMod.castHom hdq (ZMod d) s) =
      ZMod.stdAddChar (frequencyEmbedding (q := q) x * s) := by
  have hs : ZMod.castHom hdq (ZMod d) s = (s.val : ZMod d) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val s]
    simp only [map_natCast]
  have h := stdAddChar_frequency_lift hdq ((x.val : ℤ) * s.val)
  simp only [Int.cast_mul, Int.cast_natCast] at h
  rw [hs, ← ZMod.natCast_zmod_val x]
  simpa only [frequencyEmbedding, ZMod.natCast_zmod_val, mul_assoc] using h.symm

theorem normalized_phase_sum {q : ℕ} [NeZero q] (v : ZMod q) :
    (∑ s : ZMod q, ZMod.stdAddChar (s * v)) / (q : ℂ) =
      if v = 0 then 1 else 0 := by
  rw [AddChar.sum_mulShift v (ZMod.isPrimitive_stdAddChar q)]
  split_ifs <;> simp_all [ZMod.card, NeZero.ne q]

end Ostmann.QuadraticCenter

end

end OAI
