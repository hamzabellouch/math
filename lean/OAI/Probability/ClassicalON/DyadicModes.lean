import OAI.Probability.ClassicalON.DyadicSine

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON

variable {k : ℕ}

def groupedPoint (m s : Bool) (p : DyadicFreq k) : ℤ × ℤ :=
  let q := if m then (dyadicPoint p).swap else dyadicPoint p
  if s then -q else q

def groupedTorusPoint (m s : Bool) (p : DyadicFreq k) : DiscreteTorus (16*2^k) :=
  (((groupedPoint m s p).1:ZMod (16*2^k)), ((groupedPoint m s p).2:ZMod (16*2^k)))

instance dyadicModulus_neZero (k : ℕ) : NeZero (16*2^k) := ⟨by positivity⟩

theorem groupedTorusPoint_injective (m s : Bool) :
    Function.Injective (groupedTorusPoint (k := k) m s) := by
  have hs := dyadicTorusPoint_injective (k := k)
  cases m <;> cases s <;> intro p q h <;> apply hs
  · exact h
  · simpa [groupedTorusPoint, groupedPoint, dyadicTorusPoint, Prod.ext_iff] using h
  · exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  · have h' : (dyadicTorusPoint p).swap = (dyadicTorusPoint q).swap := by
      simpa [groupedTorusPoint, groupedPoint, dyadicTorusPoint, Prod.ext_iff] using h
    exact Prod.swap_injective h'

def dyadicWeight (p : DyadicFreq k) : ℝ :=
  1/((dyadicRadius p:ℝ)*Real.sqrt (dyadicRadius p:ℝ))

theorem dyadicWeight_pos (p : DyadicFreq k) : 0 < dyadicWeight p := by
  have h : (0:ℝ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
  unfold dyadicWeight
  positivity

@[simp] theorem dyadicWeight_sq (p : DyadicFreq k) :
    dyadicWeight p^2 = (1/(dyadicRadius p:ℝ))^3 := by
  have hr : (0:ℝ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
  unfold dyadicWeight
  rw [div_pow, mul_pow, Real.sq_sqrt hr.le]
  field_simp

@[simp] theorem dyadicWeight_mul_sqrt (p : DyadicFreq k) :
    dyadicWeight p*Real.sqrt (dyadicRadius p:ℝ) = 1/(dyadicRadius p:ℝ) := by
  have hr : (0:ℝ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
  have hs : Real.sqrt (dyadicRadius p:ℝ) ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  unfold dyadicWeight
  field_simp

theorem wave_commutator (a b c θ : ℝ) (w : ℂ) (hw : ‖w‖=1) :
    ((a*b:ℝ):ℂ)*w * conj (((a*c:ℝ):ℂ)*w*Complex.exp (Complex.I*(θ:ℂ))) / 2 -
      conj (((a*b:ℝ):ℂ)*w) * (((a*c:ℝ):ℂ)*w*Complex.exp (Complex.I*(θ:ℂ))) / 2 =
        -Complex.I * ((a^2*b*c*Real.sin θ:ℝ):ℂ) := by
  have hww : w*conj w=1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]; norm_num
  rw [mul_comm Complex.I (θ:ℂ), Complex.exp_ofReal_mul_I]
  simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  linear_combination -Complex.I*(a:ℂ)^2*(b:ℂ)*(c:ℂ)*(Complex.sin (θ:ℂ)) * hww

end ClassicalON

end

end OAI
