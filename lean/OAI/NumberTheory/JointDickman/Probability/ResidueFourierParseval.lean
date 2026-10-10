import OAI.NumberTheory.JointDickman.Amplification.RamanujanSum
import Mathlib.Analysis.Fourier.ZMod

namespace OAI

/-! # Exact unit-residue Parseval identity for the fine histograms -/

namespace JointDickman
open Finset
open scoped ComplexConjugate

theorem stdAddChar_conj {q : ℕ} [NeZero q] (r : ZMod q) :
    conj (ZMod.stdAddChar r) = ZMod.stdAddChar (-r) := by
  rw [← Complex.inv_eq_conj (norm_stdAddChar r),AddChar.map_neg_eq_inv]

theorem unitResidue_fourier_pair {q : ℕ} [NeZero q]
    (r s : (ZMod q)ˣ) (v w : ℂ) :
    (∑ h : ZMod q, (ZMod.stdAddChar (h*(r : ZMod q))*v)*
      conj (ZMod.stdAddChar (h*(s : ZMod q))*w)) =
      if r = s then (q : ℂ)*v*conj w else 0 := by
  have he (h : ZMod q) : (ZMod.stdAddChar (h*(r : ZMod q))*v)*
      conj (ZMod.stdAddChar (h*(s : ZMod q))*w) =
      (v*conj w)*ZMod.stdAddChar (h*((r : ZMod q)-(s : ZMod q))) := by
    rw [map_mul (starRingEnd ℂ),stdAddChar_conj,mul_sub,AddChar.map_sub_eq_div,AddChar.map_neg_eq_inv]
    ring
  simp_rw [he]
  rw [← mul_sum,AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
  have hz : (r : ZMod q)-(s : ZMod q) = 0 ↔ r = s := by
    rw [sub_eq_zero]
    exact Units.val_injective.eq_iff
  simp only [hz,ZMod.card]
  by_cases hrs : r = s
  · simp [hrs]
    ring
  · simp [hrs]

noncomputable def unitResidueFourier {q : ℕ} [NeZero q]
    (v : (ZMod q)ˣ → ℂ) (h : ZMod q) : ℂ :=
  ∑ r : (ZMod q)ˣ, ZMod.stdAddChar (h*(r : ZMod q))*v r

theorem unitResidue_fourier_parseval {q : ℕ} [NeZero q]
    (v : (ZMod q)ˣ → ℂ) :
    (∑ h : ZMod q, ‖unitResidueFourier v h‖^2) =
      (q : ℝ)*∑ r : (ZMod q)ˣ, ‖v r‖^2 := by
  have he : (∑ h : ZMod q, unitResidueFourier v h*conj (unitResidueFourier v h)) =
      ∑ r : (ZMod q)ˣ, ∑ s : (ZMod q)ˣ, ∑ h : ZMod q,
        (ZMod.stdAddChar (h*(r : ZMod q))*v r)*conj (ZMod.stdAddChar (h*(s : ZMod q))*v s) := by
    simp only [unitResidueFourier,map_sum,mul_sum,sum_mul]
    rw [sum_comm]
    conv_rhs => rw [sum_comm]
    apply sum_congr rfl
    intro s _
    rw [sum_comm]
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_natCast,Complex.ofReal_pow]
  simp_rw [← Complex.mul_conj']
  rw [he]
  simp_rw [unitResidue_fourier_pair]
  rw [mul_sum]
  apply sum_congr rfl
  intro r _
  rw [sum_eq_single r]
  · simp [mul_assoc]
  · intro s _ hsr
    simp [Ne.symm hsr]
  · simp

/-- Dividing the transform by phi gives the manuscript's probability normalization. -/
theorem normalizedUnitResidue_fourier_parseval {q : ℕ} [NeZero q]
    (v : (ZMod q)ˣ → ℂ) :
    (∑ h : ZMod q, ‖unitResidueFourier v h/(q.totient : ℂ)‖^2) =
      ((q : ℝ)/(q.totient : ℝ))*((1/(q.totient : ℝ))*∑ r : (ZMod q)ˣ, ‖v r‖^2) := by
  simp only [norm_div,Complex.norm_natCast,div_pow,← sum_div,unitResidue_fourier_parseval]
  ring

end JointDickman

end OAI
