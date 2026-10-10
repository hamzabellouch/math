import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.CenteredPhysicalThresholdProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.CoulombPairSumProgram

namespace OAI

/-! The complete scalar shift in the unit-charge construction. Input endpoints
already contain the exact mediator offset. The remaining finite shift is the
sum of edge weights and the off-site Coulomb energy; only the latter and the
one-particle reference require numerical approximation. -/

noncomputable section
namespace ContinuumCoulomb.AffinePhysicalThreshold

abbrev Input := CenteredPhysicalThreshold.Input × (ℚ × (List CoulombPairSum.Point × List ℚ))

def pairPrecision (x : Input) : ℕ :=
  (8*x.1.1.1^3+1)*(2*(x.1.2.2.1+1))

def pairValue (rho : ℕ) (x : Input) : ℚ :=
  CoulombPairSum.value rho (pairPrecision x,x.2.2.1)

def finiteValue (rho : ℕ) (x : Input) : ℚ×ℚ :=
  (x.2.1^2*(x.1.2.2.2.1-x.2.2.2.sum)-pairValue rho x,
   x.2.1^2*(x.1.2.2.2.2-x.2.2.2.sum)-pairValue rho x)

def argument (rho : ℕ) (x : Input) : CenteredPhysicalThreshold.Input :=
  (x.1.1,(x.1.2.1,(2*(x.1.2.2.1+1),finiteValue rho x)))

def value (rho : ℕ) (x : Input) : ℚ×ℚ :=
  CenteredPhysicalThreshold.value rho (argument rho x)

def exactFinite (x : Input) (v : ℝ) : ℝ×ℝ :=
  ((x.2.1:ℝ)^2*((x.1.2.2.2.1:ℝ)-(x.2.2.2.sum:ℝ))-v,
   (x.2.1:ℝ)^2*((x.1.2.2.2.2:ℝ)-(x.2.2.2.sum:ℝ))-v)

def exactValue (rho : ℕ) (x : Input) (v : ℝ) : ℝ×ℝ :=
  (CenteredPhysicalThreshold.actualOffset rho x.1+
      (CenteredPhysicalThreshold.amplification rho x.1.1.1:ℝ)*(exactFinite x v).1,
   CenteredPhysicalThreshold.actualOffset rho x.1+
      (CenteredPhysicalThreshold.amplification rho x.1.1.1:ℝ)*(exactFinite x v).2)

theorem pair_budget (rho : ℕ) (hrho : 0 < rho) (x : Input) :
    (CenteredPhysicalThreshold.amplification rho x.1.1.1:ℝ)/(pairPrecision x+1:ℝ) ≤
      1/(2*((x.1.2.2.1:ℝ)+1)) := by
  have ha := CenteredPhysicalThreshold.amplification_bound rho x.1.1.1 hrho
  have hp : 0 < 2*((x.1.2.2.1:ℝ)+1) := by positivity
  have hd : 0 < (pairPrecision x:ℝ)+1 := by positivity
  apply (div_le_div_iff₀ hd hp).mpr
  have hm := mul_le_mul_of_nonneg_right ha.2 hp.le
  simp only [pairPrecision,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow,
    Nat.cast_ofNat]
  nlinarith

theorem reference_budget (x : Input) :
    1/((2*(x.1.2.2.1+1):ℕ)+1:ℝ) ≤ 1/(2*((x.1.2.2.1:ℝ)+1)) := by
  apply one_div_le_one_div_of_le (by positivity)
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  linarith

theorem value_error (rho : ℕ) (hrho : 0 < rho) (x : Input)
    (hmesh : 0 < x.1.1.1) (v : ℝ)
    (hv : |(pairValue rho x:ℝ)-v| ≤ 1/(pairPrecision x+1:ℝ)) :
    |((value rho x).1:ℝ)-(exactValue rho x v).1| ≤ 1/(x.1.2.2.1+1:ℝ) ∧
    |((value rho x).2:ℝ)-(exactValue rho x v).2| ≤ 1/(x.1.2.2.1+1:ℝ) := by
  have ha := CenteredPhysicalThreshold.amplification_bound rho x.1.1.1 hrho
  have hp : 0 < (x.1.2.2.1:ℝ)+1 := by positivity
  have hoff := (CenteredPhysicalThreshold.offset_error rho hrho (argument rho x) hmesh).trans
    (reference_budget x)
  have hpair : (CenteredPhysicalThreshold.amplification rho x.1.1.1:ℝ)*
      |(pairValue rho x:ℝ)-v| ≤ 1/(2*((x.1.2.2.1:ℝ)+1)) := by
    apply (mul_le_mul_of_nonneg_left hv ha.1).trans
    simpa only [mul_one_div] using pair_budget rho hrho x
  have hsum : 1/(2*((x.1.2.2.1:ℝ)+1))+1/(2*((x.1.2.2.1:ℝ)+1)) =
      1/((x.1.2.2.1:ℝ)+1) := by
    field_simp [hp.ne']
    ring
  have hid1 : ((value rho x).1:ℝ)-(exactValue rho x v).1 =
      ((CenteredPhysicalThreshold.offset rho (argument rho x):ℝ)-CenteredPhysicalThreshold.actualOffset rho x.1)-
      (CenteredPhysicalThreshold.amplification rho x.1.1.1:ℝ)*((pairValue rho x:ℝ)-v) := by
    simp only [value,CenteredPhysicalThreshold.value,exactValue,exactFinite,argument,finiteValue,
      Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_pow]
    ring
  have hid2 : ((value rho x).2:ℝ)-(exactValue rho x v).2 =
      ((CenteredPhysicalThreshold.offset rho (argument rho x):ℝ)-CenteredPhysicalThreshold.actualOffset rho x.1)-
      (CenteredPhysicalThreshold.amplification rho x.1.1.1:ℝ)*((pairValue rho x:ℝ)-v) := by
    simp only [value,CenteredPhysicalThreshold.value,exactValue,exactFinite,argument,finiteValue,
      Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_pow]
    ring
  have hoff' : |(CenteredPhysicalThreshold.offset rho (argument rho x):ℝ)-
      CenteredPhysicalThreshold.actualOffset rho x.1| ≤ 1/(2*((x.1.2.2.1:ℝ)+1)) := hoff
  have htri := abs_sub_le ((CenteredPhysicalThreshold.offset rho (argument rho x):ℝ)-
    CenteredPhysicalThreshold.actualOffset rho x.1) 0
    ((CenteredPhysicalThreshold.amplification rho x.1.1.1:ℝ)*((pairValue rho x:ℝ)-v))
  simp only [sub_zero,zero_sub,abs_neg] at htri
  have hbound := htri.trans
    (add_le_add hoff' (by simpa only [abs_mul,abs_of_nonneg ha.1] using hpair))
  rw [hsum] at hbound
  constructor
  · rw [hid1]
    exact hbound
  · rw [hid2]
    exact hbound

theorem actual_error (rho : ℕ) (hrho : 0 < rho) (x : Input)
    (hmesh : 0 < x.1.1.1) {m : ℕ}
    (u : Fin m → CoulombPairSum.Point) (hu : Function.Injective u)
    (hsites : x.2.2.1 = List.ofFn u) :
    let v := CoulombPairSum.exactTotal (GaussianFrequency.frequency rho) u
    |((value rho x).1:ℝ)-(exactValue rho x v).1| ≤ 1/(x.1.2.2.1+1:ℝ) ∧
    |((value rho x).2:ℝ)-(exactValue rho x v).2| ≤ 1/(x.1.2.2.1+1:ℝ) := by
  apply value_error rho hrho x hmesh
  simpa only [pairValue,hsites] using
    CoulombPairSum.error rho (pairPrecision x) hrho u hu

theorem gap (rho : ℕ) (x : Input) :
    (value rho x).2-(value rho x).1 =
      CenteredPhysicalThreshold.amplification rho x.1.1.1*x.2.1^2*
        (x.1.2.2.2.2-x.1.2.2.2.1) := by
  rw [value,CenteredPhysicalThreshold.gap]
  simp only [argument,finiteValue]
  ring

end ContinuumCoulomb.AffinePhysicalThreshold

end

end OAI
