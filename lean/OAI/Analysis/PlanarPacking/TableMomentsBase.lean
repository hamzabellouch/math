import OAI.Analysis.PlanarPacking.NodeIntervals
import OAI.Analysis.PlanarPacking.TableDensityBase
import OAI.Analysis.PlanarPacking.MomentRecurrence

namespace OAI

/-! # Certified quadrature and atomic bounds for the Gaussian moments -/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid Numerical
open scoped BigOperators

noncomputable def tableMomentRule (a : Bool) (m : ℝ) (ell : ℕ) : ℂ :=
  ∑ j : Fin 6, pieceRule (fun t => tableDensity a j.val t * complexTransformedFactor m 1 ell t) j.val
noncomputable def tableMomentIntegral (a : Bool) (m : ℝ) (ell : ℕ) : ℂ :=
  ∑ j : Fin 6, pieceIntegral (fun t => tableDensity a j.val t * complexTransformedFactor m 1 ell t) j.val
noncomputable def tableMomentAtom (a : Bool) (m : ℝ) (ell : ℕ) : ℂ :=
  ((tableConstant a:ℝ):ℂ) * ∑ j : Fin 7,
    (if j.val=0 then 1 else 2) * Pcoeff j.val *
      complexTransformedFactor m 1 ell ((j.val:ℝ)/6)
noncomputable def tableMomentK (a : Bool) (m : ℝ) (ell : ℕ) : ℝ :=
  (tableMomentAtom a m ell + tableMomentIntegral a m ell).re

lemma tableMoment_error (a : Bool) {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100) (ell : ℕ) :
    ‖tableMomentIntegral a m ell-tableMomentRule a m ell‖ < 1/10^22 :=
  transformedMoment_rule_error _ _ (table_range_mass a) hm0 hm1 (by norm_num) ell

lemma table_kernel_zero_contains {box : CBox} {t : ℝ} {m : ℕ}
    (ha : box.Contains ((lambda t * Complex.exp (Complex.I*Real.pi*z t*m))*1)) :
    box.Contains (complexTransformedFactor m 1 0 t) := by
  exact transformed_factor_zero_contains (by simpa only [mul_one] using ha)
lemma table_kernel_one_contains {box : CBox} {t : ℝ} {m : ℕ}
    (ha : box.Contains ((lambda t * Complex.exp (Complex.I*Real.pi*z t*m))*(Complex.I*Real.pi*z t))) :
    box.Contains (complexTransformedFactor m 1 1 t) := by
  simpa only [complexTransformedFactor,complexZ_ofReal,complexLambda_ofReal,pow_one,
    Nat.factorial_one,Nat.cast_one,div_one,Complex.ofReal_one,mul_one,Complex.ofReal_natCast] using ha

def tableAtomBox (a : Bool) (kernel : Fin 7 → CBox) : CBox :=
  (finSum (fun j : Fin 7 => ((coefficientBox j.val).scale (if j.val=0 then 1 else 2) 1).mul (kernel j))).scale (if a then 17 else -13) 1000
lemma tableAtomBox_contains (a : Bool) {kernel : Fin 7 → CBox} {m : ℝ} {ell : ℕ}
    (hk : ∀ j, (kernel j).Contains (complexTransformedFactor m 1 ell ((j.val:ℝ)/6))) :
    (tableAtomBox a kernel).Contains (tableMomentAtom a m ell) := by
  have hh := finSum_contains (fun j : Fin 7 => CBox.contains_mul
    (CBox.contains_scale (coefficientBox_contains j.val) (if j.val=0 then 1 else 2) 1 (by norm_num)) (hk j))
  have hs := CBox.contains_scale hh (if a then 17 else -13) 1000 (by norm_num)
  change (tableAtomBox a kernel).Contains _ at hs
  convert hs using 1
  cases a <;> simp [tableMomentAtom,tableConstant]


lemma tableMomentK_contains {a : Bool} {m : ℝ} {ell : ℕ} {ab rb : CBox}
    (ha : ab.Contains (tableMomentAtom a m ell))
    (hr : rb.Contains (tableMomentRule a m ell)) (hm0 : 0 ≤ m) (hm1 : m ≤ 100) :
    (inflate (ab.add rb).re).Contains (tableMomentK a m ell) := by
  apply inflate_contains (CBox.contains_add ha hr).1
  unfold tableMomentK
  have he := (Complex.abs_re_le_norm (tableMomentIntegral a m ell-tableMomentRule a m ell)).trans_lt
    (tableMoment_error a hm0 hm1 ell)
  simpa only [Complex.add_re,Complex.sub_re,add_sub_add_left_eq_sub] using he
end SharpPlanar

end OAI
