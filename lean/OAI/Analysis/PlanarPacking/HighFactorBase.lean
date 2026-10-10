import OAI.Analysis.PlanarPacking.MomentRecurrence
import OAI.Analysis.PlanarPacking.Grid

namespace OAI

/-! # Interval bounds for the normalized Gaussian moment powers -/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid
noncomputable def momentPower (ell : ℕ) (t : ℂ) : ℂ :=
  (Complex.I*Real.pi*t)^ell/(ell.factorial:ℂ)
lemma momentPower_zero (t : ℂ) : momentPower 0 t = 1 := by simp [momentPower]
lemma momentPower_step (ell : ℕ) (t : ℂ) :
    momentPower (ell+1) t = momentPower ell t * (Complex.I*Real.pi*t)/((ell+1:ℕ):ℂ) := by
  unfold momentPower
  simp only [pow_succ,Nat.factorial_succ,Nat.cast_mul]
  ring
lemma momentPower_step_contains {a b : CBox} {t : ℂ} {ell : ℕ}
    (ha : a.Contains (momentPower ell t)) (hb : b.Contains (Complex.I*Real.pi*t)) :
    ((a.mul b).scale 1 (ell+1)).Contains (momentPower (ell+1) t) := by
  rw [momentPower_step]
  exact factor_step_contains ha hb ell
lemma momentPower_zero_contains (t : ℂ) : (CBox.rat 1 1 0 1).Contains (momentPower 0 t) := by
  simpa [momentPower_zero] using CBox.contains_rat 1 1 0 1 (by norm_num) (by norm_num)
lemma momentPower_direct_step_contains (j : Fin 6) (i k : Fin 16) :
    (piI.mul (rcast (gridRows j i k).t)).Contains
      (Complex.I*Real.pi*(quadraturePoint j.val (16*i.val+k.val):ℂ)) := by
  exact CBox.contains_mul piI_contains (rcast_contains (gridRows_contains j i k).1)
lemma momentPower_trans_step_contains (j : Fin 6) (i k : Fin 16) :
    (piI.mul (gridRows j i k).z).Contains
      (Complex.I*Real.pi*(z (quadraturePoint j.val (16*i.val+k.val)))) := by
  have hz := (gridRows_contains j i k).2.2.1
  rw [pointZ_eq] at hz
  exact CBox.contains_mul piI_contains hz
lemma momentPower_direct_contains {a b : CBox} {t : ℝ} {m ell : ℕ}
    (ha : a.Contains (Complex.exp (-Complex.I*Real.pi*t*m)))
    (hb : b.Contains (momentPower ell t)) :
    (a.conj.mul b).Contains (complexDirectFactor m 1 ell t) := by
  have hh := CBox.contains_mul (direct_factor_zero_contains ha) hb
  simpa only [complexDirectFactor,Complex.ofReal_one,mul_one,pow_zero,Nat.factorial_zero,
    Nat.cast_one,div_one,momentPower,mul_div_assoc] using hh
lemma momentPower_trans_contains {a b : CBox} {t : ℝ} {m ell : ℕ}
    (ha : a.Contains ((lambda t*Complex.exp (Complex.I*Real.pi*z t*m))*1))
    (hb : b.Contains (momentPower ell (z t))) :
    (a.mul b).Contains (complexTransformedFactor m 1 ell t) := by
  have hh := CBox.contains_mul ha hb
  simpa only [complexTransformedFactor,Complex.ofReal_one,complexLambda_ofReal,
    complexZ_ofReal,mul_one,momentPower,mul_div_assoc,Complex.ofReal_natCast] using hh
end SharpPlanar

end OAI
