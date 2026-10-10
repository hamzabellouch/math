import OAI.Geometry.RCD.Transport.EntropicDirectionalBound

namespace OAI

/-! # The explicit entropy-power barrier and its initial rate -/

noncomputable section
namespace RegularPointCoordinates

def entropyPowerChord (c A B t : ℝ) : ℝ :=
  if c=0 then (1-t)*A+t*B else hyperbolicChord (Real.sqrt c) A B t

def entropyPowerChordDerivative (c A B : ℝ) : ℝ :=
  if c=0 then B-A else Real.sqrt c*(B-Real.cosh (Real.sqrt c)*A)/Real.sinh (Real.sqrt c)

def entropyPowerRate (N c A B : ℝ) : ℝ :=
  if c=0 then N*(1-B/A) else N*Real.sqrt c/Real.sinh (Real.sqrt c)*(Real.cosh (Real.sqrt c)-B/A)

@[simp] theorem entropyPowerChord_zero {c : ℝ} (hc : 0 ≤ c) (A B : ℝ) :
    entropyPowerChord c A B 0=A := by
  by_cases h : c=0
  · simp [entropyPowerChord,h]
  · simp [entropyPowerChord,h,hyperbolicChord_zero (Real.sqrt_pos.mpr (lt_of_le_of_ne hc (Ne.symm h)))]

theorem hasDerivAt_entropyPowerChord_zero (c A B : ℝ) :
    HasDerivAt (entropyPowerChord c A B) (entropyPowerChordDerivative c A B) 0 := by
  unfold entropyPowerChord entropyPowerChordDerivative
  by_cases hc : c=0
  · simp only [hc,↓reduceIte]
    convert (((hasDerivAt_id (0:ℝ)).const_sub 1).mul_const A).add
      ((hasDerivAt_id (0:ℝ)).mul_const B) using 1
    · ext t
      simp only [Pi.add_apply,id_eq]
    · ring
  · simpa only [hc,↓reduceIte] using
      hasDerivAt_hyperbolicChord_zero (Real.sqrt c) A B

theorem entropyPowerRate_eq {N c A B : ℝ} (hc : 0 ≤ c) (hA : 0 < A) :
    entropyPowerRate N c A B = -N*(entropyPowerChordDerivative c A B/A) := by
  by_cases h : c=0
  · simp only [entropyPowerRate,entropyPowerChordDerivative,h,↓reduceIte]
    field_simp [hA.ne']
    ring
  · have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr (lt_of_le_of_ne hc (Ne.symm h))
    simp only [entropyPowerRate,entropyPowerChordDerivative,h,↓reduceIte]
    field_simp [hA.ne',(Real.sinh_pos_iff.mpr hs).ne']
    ring

end RegularPointCoordinates

end

end OAI
