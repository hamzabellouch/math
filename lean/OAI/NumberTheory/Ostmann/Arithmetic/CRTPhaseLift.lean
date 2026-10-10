import OAI.NumberTheory.Ostmann.Characters.CRTFourier
import OAI.NumberTheory.Ostmann.QuadraticCenter.RealQuadraticPhase

namespace OAI

/-! # Identifying the CRT phase with the common real translation -/

namespace Ostmann

theorem crt_translation_phase {d M : ℕ} [NeZero d] [NeZero M]
    (h : d.Coprime M) (t : ZMod M) (h₀ u : ℤ)
    (hlift : (d : ℤ) ∣ (t.val : ℤ) + (M : ℤ) * h₀) :
    ZMod.stdAddChar (t * ((d : ZMod M)⁻¹ * (u : ZMod M))) =
      realAdditivePhase ((((t.val : ℝ) / M + h₀) * u) / d) := by
  obtain ⟨k, hk⟩ := hlift
  have hd : IsUnit (d : ZMod M) := (ZMod.isUnit_iff_coprime d M).mpr h
  have hkmod : (d : ZMod M) * (k : ZMod M) = t := by
    have hh := congrArg (fun z : ℤ => (z : ZMod M)) hk
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      zero_mul, add_zero, ZMod.natCast_zmod_val] using hh.symm
  have hkinv : (d : ZMod M)⁻¹ * t = (k : ZMod M) := by
    rw [← hkmod, ← mul_assoc, ZMod.inv_mul_of_unit _ hd, one_mul]
  have harg : t * ((d : ZMod M)⁻¹ * (u : ZMod M)) = ((k * u : ℤ) : ZMod M) := by
    rw [Int.cast_mul, ← hkinv]
    ring
  have hkreal : (t.val : ℝ) + (M : ℝ) * h₀ = (d : ℝ) * k := by exact_mod_cast hk
  have hreal : (((t.val : ℝ) / M + h₀) * u) / d = ((k * u : ℤ) : ℝ) / M := by
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
    have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
    calc
      _ = ((t.val : ℝ) + M * h₀) * u / ((M : ℝ) * d) := by field_simp
      _ = _ := by rw [hkreal]; push_cast; field_simp
  rw [harg, hreal, ZMod.stdAddChar_coe]
  unfold realAdditivePhase
  congr 1
  push_cast
  ring

end Ostmann

end OAI
