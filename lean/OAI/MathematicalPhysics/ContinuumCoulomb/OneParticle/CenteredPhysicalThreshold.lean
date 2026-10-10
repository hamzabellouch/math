import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.SlabBoxProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.PhysicalThreshold
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.GaussianFrequencyProgram

namespace OAI

/-! Physical threshold reference for the exact half-cell boundary of the
centered grid. The finite threshold is scaled by lambda and the true rational
slab reference by lambda squared times the electron count. -/

noncomputable section
namespace ContinuumCoulomb.CenteredPhysicalThreshold

abbrev Geometry := ℕ × (ℕ × ℕ)
abbrev Input := Geometry × (ℕ × (ℕ × (ℚ × ℚ)))

def amplification (rho mesh : ℕ) : ℚ := 8*(mesh:ℚ)^3/rho

def precision (x : Input) : ℕ :=
  8*(8*x.1.1^3+1)^2*(x.2.1+1)*(x.2.2.1+1)

def reference (rho : ℕ) (x : Input) : ℚ :=
  SlabBoxSchedule.value rho (SlabBoxSchedule.centered (precision x) x.1.1 x.1.2.1 x.1.2.2)+
    (GaussianFrequency.approximate rho (precision x)-1)/2

def offset (rho : ℕ) (x : Input) : ℚ :=
  amplification rho x.1.1^2*x.2.1*reference rho x

def value (rho : ℕ) (x : Input) : ℚ×ℚ :=
  (offset rho x+amplification rho x.1.1*x.2.2.2.1,
   offset rho x+amplification rho x.1.1*x.2.2.2.2)

def actualReference (rho : ℕ) (g : Geometry) : ℝ :=
  slabPotential (rho:ℝ) (SlabBoxSchedule.centeredWidth g.2.1 g.1:ℝ)
    (SlabBoxSchedule.centeredWidth g.2.2 g.1:ℝ) 0+(GaussianFrequency.frequency rho-1)/2

def actualOffset (rho : ℕ) (x : Input) : ℝ :=
  (amplification rho x.1.1:ℝ)^2*(x.2.1:ℝ)*actualReference rho x.1

theorem reference_error (rho : ℕ) (x : Input) (hmesh : 0 < x.1.1) :
    |(reference rho x:ℝ)-actualReference rho x.1| ≤
      2/(precision x+1:ℝ) := by
  have hs := SlabBoxSchedule.centered_error rho (precision x) x.1.1 x.1.2.1 x.1.2.2 hmesh
  rw [← SlabBoxSchedule.centeredWidth_real,← SlabBoxSchedule.centeredWidth_real] at hs
  have hf := GaussianFrequency.approximation_error rho (precision x)
  have he : (reference rho x:ℝ)-actualReference rho x.1 =
      ((SlabBoxSchedule.value rho (SlabBoxSchedule.centered (precision x) x.1.1 x.1.2.1 x.1.2.2):ℝ)-
        slabPotential (rho:ℝ) (SlabBoxSchedule.centeredWidth x.1.2.1 x.1.1:ℝ)
        (SlabBoxSchedule.centeredWidth x.1.2.2 x.1.1:ℝ) 0)+
      ((GaussianFrequency.approximate rho (precision x):ℝ)-GaussianFrequency.frequency rho)/2 := by
    simp only [reference,actualReference,Rat.cast_add,Rat.cast_sub,Rat.cast_div,Rat.cast_one,
      Rat.cast_ofNat]
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hn : 0 ≤ ((precision x:ℝ)+1)⁻¹ := by positivity
  simp only [div_eq_mul_inv] at hs ⊢
  nlinarith

theorem amplification_bound (rho mesh : ℕ) (hrho : 0 < rho) :
    0 ≤ (amplification rho mesh:ℝ) ∧ (amplification rho mesh:ℝ) ≤ 8*(mesh:ℝ)^3 := by
  have hp : 0 < (rho:ℝ) := by exact_mod_cast hrho
  have h1 : 1 ≤ (rho:ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hrho)
  simp only [amplification,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_pow,Rat.cast_natCast]
  constructor
  · positivity
  · exact div_le_self (by positivity) h1

theorem offset_error (rho : ℕ) (hrho : 0 < rho) (x : Input) (hmesh : 0 < x.1.1) :
    |(offset rho x:ℝ)-actualOffset rho x| ≤ 1/(x.2.2.1+1:ℝ) := by
  have he := reference_error rho x hmesh
  have ha := amplification_bound rho x.1.1 hrho
  have hsq : (amplification rho x.1.1:ℝ)^2 ≤ (8*(x.1.1:ℝ)^3+1)^2 := by
    nlinarith
  have hcoef : (amplification rho x.1.1:ℝ)^2*(x.2.1:ℝ)*2 ≤
      8*(8*(x.1.1:ℝ)^3+1)^2*((x.2.1:ℝ)+1) := by
    have ht := mul_le_mul_of_nonneg_right hsq (Nat.cast_nonneg x.2.1)
    nlinarith [sq_nonneg (8*(x.1.1:ℝ)^3+1)]
  have hprec : (precision x:ℝ) =
      8*(8*(x.1.1:ℝ)^3+1)^2*((x.2.1:ℝ)+1)*((x.2.2.1:ℝ)+1) := by
    simp [precision]
  have hden : 0 < (precision x:ℝ)+1 := by positivity
  have hp : 0 < (x.2.2.1:ℝ)+1 := by positivity
  have hprod : (amplification rho x.1.1:ℝ)^2*(x.2.1:ℝ)*2*((x.2.2.1:ℝ)+1) ≤
      (precision x:ℝ)+1 := by
    rw [hprec]
    nlinarith [mul_le_mul_of_nonneg_right hcoef hp.le]
  have hid : (offset rho x:ℝ)-actualOffset rho x =
      (amplification rho x.1.1:ℝ)^2*(x.2.1:ℝ)*
        ((reference rho x:ℝ)-actualReference rho x.1) := by
    simp only [offset,actualOffset,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast]
    ring
  rw [hid,abs_mul,abs_of_nonneg (by positivity : 0 ≤ (amplification rho x.1.1:ℝ)^2*(x.2.1:ℝ))]
  apply (mul_le_mul_of_nonneg_left he (by positivity)).trans
  apply (le_div_iff₀ hp).mpr
  calc
    _ = ((amplification rho x.1.1:ℝ)^2*(x.2.1:ℝ)*2*
        ((x.2.2.1:ℝ)+1))/((precision x:ℝ)+1) := by ring
    _ ≤ 1 := (div_le_one hden).mpr hprod

theorem lower_error (rho : ℕ) (hrho : 0 < rho) (x : Input) (hmesh : 0 < x.1.1) :
    |((value rho x).1:ℝ)-(actualOffset rho x+
      (amplification rho x.1.1:ℝ)*(x.2.2.2.1:ℝ))| ≤ 1/(x.2.2.1+1:ℝ) := by
  simpa only [value,Rat.cast_add,Rat.cast_mul,add_sub_add_right_eq_sub] using offset_error rho hrho x hmesh

theorem upper_error (rho : ℕ) (hrho : 0 < rho) (x : Input) (hmesh : 0 < x.1.1) :
    |((value rho x).2:ℝ)-(actualOffset rho x+
      (amplification rho x.1.1:ℝ)*(x.2.2.2.2:ℝ))| ≤ 1/(x.2.2.1+1:ℝ) := by
  simpa only [value,Rat.cast_add,Rat.cast_mul,add_sub_add_right_eq_sub] using offset_error rho hrho x hmesh

theorem gap (rho : ℕ) (x : Input) :
    (value rho x).2-(value rho x).1 = amplification rho x.1.1*(x.2.2.2.2-x.2.2.2.1) := by
  unfold value
  ring

end ContinuumCoulomb.CenteredPhysicalThreshold

end

end OAI
