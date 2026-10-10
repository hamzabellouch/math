import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZSample

namespace OAI

/-! Logarithmic precision, computed from binary numerators, suffices for the physical error budget. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open ExactQuantumFactoring.BitStackProgram

def precision (q : ℚ) (N : ℕ) : ℕ := q.num.natAbs.size+N.size

theorem rational_le_numerator (q : ℚ) : (q:ℝ) ≤ (q.num.natAbs:ℝ) := by
  have hden : (1:ℝ) ≤ q.den := by exact_mod_cast q.pos
  have he : (q:ℝ) = (q.num:ℝ)/(q.den:ℝ) := by
    exact_mod_cast (Rat.num_div_den q).symm
  have habs : |(q.num:ℝ)| = (q.num.natAbs:ℝ) := by rw [Nat.cast_natAbs,Int.cast_abs]
  calc
    _ ≤ |(q:ℝ)| := le_abs_self _
    _ = |(q.num:ℝ)|/(q.den:ℝ) := by
      rw [he,abs_div,abs_of_nonneg (show (0:ℝ) ≤ q.den by exact_mod_cast Nat.zero_le q.den)]
    _ ≤ |(q.num:ℝ)| := div_le_self (abs_nonneg _) hden
    _ = _ := habs

theorem precision_error (q : ℚ) (N : ℕ) (hN : 0 < N) :
    (q:ℝ)*(2:ℝ)⁻¹^(precision q N) ≤ 1/(N:ℝ) := by
  have ha : (q.num.natAbs:ℝ) ≤ (2:ℝ)^q.num.natAbs.size := by
    exact_mod_cast (Nat.lt_size_self q.num.natAbs).le
  have hb : (N:ℝ) ≤ (2:ℝ)^N.size := by exact_mod_cast (Nat.lt_size_self N).le
  have hprod : (q:ℝ)*(N:ℝ) ≤ (2:ℝ)^(precision q N) := by
    rw [precision,pow_add]
    exact mul_le_mul ((rational_le_numerator q).trans ha) hb (Nat.cast_nonneg _) (by positivity)
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hpow : (0:ℝ) < 2^(precision q N) := by positivity
  have hdiv := (div_le_one hpow).mpr hprod
  apply (le_div_iff₀ hNp).mpr
  convert hdiv using 1
  simp only [div_eq_mul_inv,inv_pow]
  ring

def precisionCode : (ℚ × ℕ) → List Bool := prodCode ratCode Nat.bits

noncomputable opaque numeratorMagnitudeProgram : Procedure precisionCode Nat.bits
    (fun x => x.1.num.natAbs) :=
  Procedure.intAbs.comp (Procedure.ratNum.comp (Procedure.first ratCode Nat.bits))

noncomputable opaque numeratorSizeProgram : Procedure precisionCode unaryCode
    (fun x => x.1.num.natAbs.size) :=
  ((Procedure.length.precompose Nat.bits).comp numeratorMagnitudeProgram).congrFun
    (by intro x; exact Nat.size_eq_bits_len _)

noncomputable opaque denominatorSizeProgram : Procedure precisionCode unaryCode (fun x => x.2.size) :=
  ((Procedure.length.precompose Nat.bits).comp (Procedure.second ratCode Nat.bits)).congrFun
    (by intro x; exact Nat.size_eq_bits_len _)

noncomputable opaque precisionProgram : Procedure precisionCode unaryCode (fun x => precision x.1 x.2) :=
  Procedure.unaryAdd.comp (numeratorSizeProgram.pair denominatorSizeProgram)

noncomputable def precisionCertificate : Turing.TM2ComputableInPolyTime precisionCode unaryCode
    (fun x => precision x.1 x.2) := precisionProgram.toTM2

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
