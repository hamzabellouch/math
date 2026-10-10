import Mathlib.Data.ZMod.Basic
import OAI.NumberTheory.Ostmann.Construction.TransferArithmetic

namespace OAI

/-! # Equality of pivot residue keys is the exact transfer equation -/

namespace Ostmann

theorem pivot_residue_eq_iff (M L R : ℕ) (hLM : L.Coprime M) (hRM : R.Coprime M)
    (v w : ℤ) :
    (v : ZMod M) * (L : ZMod M)⁻¹ = (w : ZMod M) * (R : ZMod M)⁻¹ ↔
      (M : ℤ) ∣ v * R - w * L := by
  have hL := (ZMod.isUnit_iff_coprime L M).mpr hLM
  have hR := (ZMod.isUnit_iff_coprime R M).mpr hRM
  have hprod := hL.mul hR
  have he : ((v : ZMod M) * (L : ZMod M)⁻¹ - (w : ZMod M) * (R : ZMod M)⁻¹) *
      ((L : ZMod M) * R) = ((v * R - w * L : ℤ) : ZMod M) := by
    push_cast
    calc
      _ = (v : ZMod M) * ((L : ZMod M)⁻¹ * L) * R -
          (w : ZMod M) * ((R : ZMod M)⁻¹ * R) * L := by ring
      _ = _ := by rw [ZMod.inv_mul_of_unit _ hL, ZMod.inv_mul_of_unit _ hR]; ring
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro h
    rw [h, sub_self, zero_mul] at he
    exact he.symm
  · intro h
    rw [h] at he
    have hz := congrArg (fun a : ZMod M => a * ((L : ZMod M) * R)⁻¹) he
    rw [mul_assoc, ZMod.mul_inv_of_unit _ hprod, mul_one, zero_mul] at hz
    exact sub_eq_zero.mp hz

theorem pivot_residue_offdiagonal (M L R : ℕ) (hM : M ≠ 0)
    (hLM : L.Coprime M) (hRM : R.Coprime M) (v w : ℤ)
    (hkey : (v : ZMod M) * (L : ZMod M)⁻¹ = (w : ZMod M) * (R : ZMod M)⁻¹)
    (hoff : v * R - w * L ≠ 0) :
    ∃! s : ℤ, s ≠ 0 ∧ v * R - w * L = s * M := by
  exact unique_transferred_frequency _ M hoff (by exact_mod_cast hM)
    ((pivot_residue_eq_iff M L R hLM hRM v w).mp hkey)

end Ostmann

end OAI
