import OAI.NumberTheory.Ostmann.QuadraticCenter.PoissonPhase

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter

def centerCorrection (q L : ℕ) [NeZero L] (t : ℤ) : ℕ :=
  (-((t : ZMod L) * (q : ZMod L)⁻¹)).val

theorem centerCorrection_lt (q L : ℕ) [NeZero L] (t : ℤ) :
    centerCorrection q L t < L := ZMod.val_lt _

theorem centerCorrection_dvd {q L : ℕ} [NeZero L] (hcop : q.Coprime L) (t : ℤ) :
    (L : ℤ) ∣ t + (q : ℤ) * centerCorrection q L t := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, centerCorrection, ZMod.natCast_zmod_val]
  have hi : (q : ZMod L) * (q : ZMod L)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one q hcop
  calc
    _ = (t : ZMod L) * (1 - (q : ZMod L) * (q : ZMod L)⁻¹) := by ring
    _ = 0 := by rw [hi, sub_self, mul_zero]

theorem centerCorrection_divisor {q L d : ℕ} [NeZero L]
    (hcop : q.Coprime L) (hd : d ∣ L) (t : ℤ) :
    (d : ℤ) ∣ t + (q : ℤ) * centerCorrection q L t := by
  exact (by exact_mod_cast hd : (d : ℤ) ∣ (L : ℤ)).trans (centerCorrection_dvd hcop t)

theorem bezout_inverse_cast {q d : ℕ} [NeZero d] (hcop : q.Coprime d)
    (r s : ℤ) (hbez : (d : ℤ) * r + (q : ℤ) * s = 1) :
    (s : ZMod d) = (q : ZMod d)⁻¹ := by
  have hs : (q : ZMod d) * (s : ZMod d) = 1 := by
    have he := congrArg (fun a : ℤ => (a : ZMod d)) hbez
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      zero_mul, zero_add, Int.cast_one] using he
  have hi : (q : ZMod d) * (q : ZMod d)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one q hcop
  calc
    (s : ZMod d) = ((q : ZMod d)⁻¹ * (q : ZMod d)) * s := by rw [mul_comm _ (q : ZMod d), hi, one_mul]
    _ = (q : ZMod d)⁻¹ := by rw [mul_assoc, hs, mul_one]

theorem stdAddChar_centerCorrection {q L d : ℕ} [NeZero q] [NeZero L] [NeZero d]
    (hcop : q.Coprime L) (hd : d ∣ L) (r s t u : ℤ)
    (hbez : (d : ℤ) * r + (q : ℤ) * s = 1) :
    ZMod.stdAddChar (((u * r : ℤ) : ZMod q) * (t : ZMod q)) =
      weylPhase (((t : ℝ) / q + (centerCorrection q L t : ℝ)) * u / d) := by
  simpa only [Int.cast_natCast] using stdAddChar_common_center r s t (centerCorrection q L t) u
    hbez (centerCorrection_divisor hcop hd t)

end Ostmann.QuadraticCenter

end

end OAI
