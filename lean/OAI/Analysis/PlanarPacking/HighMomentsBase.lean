import OAI.Analysis.PlanarPacking.TableMomentsBase

namespace OAI

/-! # Interval enclosures for direct and transformed moments of arbitrary order -/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid Numerical
noncomputable def fullFactor (tr : Bool) (m : ℝ) (ell : ℕ) (t : ℂ) : ℂ :=
  if tr then complexTransformedFactor m 1 ell t else complexDirectFactor m 1 ell t
noncomputable def fullMomentRule (a tr : Bool) (m : ℝ) (ell : ℕ) : ℂ :=
  ∑ j : Fin 6, pieceRule (fun t => tableDensity a j.val t*fullFactor tr m ell t) j.val
noncomputable def fullMomentIntegral (a tr : Bool) (m : ℝ) (ell : ℕ) : ℂ :=
  ∑ j : Fin 6, pieceIntegral (fun t => tableDensity a j.val t*fullFactor tr m ell t) j.val
noncomputable def fullMomentAtom (a tr : Bool) (m : ℝ) (ell : ℕ) : ℂ :=
  ((tableConstant a:ℝ):ℂ)*∑ j : Fin 7,
    (if j.val=0 then 1 else 2)*Pcoeff j.val*fullFactor tr m ell ((j.val:ℝ)/6)
noncomputable def fullMoment (a tr : Bool) (m : ℝ) (ell : ℕ) : ℝ :=
  (fullMomentAtom a tr m ell+fullMomentIntegral a tr m ell).re
lemma fullMoment_error (a tr : Bool) {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100) (ell : ℕ) :
    ‖fullMomentIntegral a tr m ell-fullMomentRule a tr m ell‖ < 1/10^22 := by
  cases tr
  · exact directMoment_rule_error _ _ (table_range_mass a) hm0 hm1 (by norm_num) ell
  · exact transformedMoment_rule_error _ _ (table_range_mass a) hm0 hm1 (by norm_num) ell
lemma fullAtomBox_contains (a tr : Bool) {kernel : Fin 7 → CBox} {m : ℝ} {ell : ℕ}
    (hk : ∀ j, (kernel j).Contains (fullFactor tr m ell ((j.val:ℝ)/6))) :
    (tableAtomBox a kernel).Contains (fullMomentAtom a tr m ell) := by
  have hh := finSum_contains (fun j : Fin 7 => CBox.contains_mul
    (CBox.contains_scale (coefficientBox_contains j.val) (if j.val=0 then 1 else 2) 1 (by norm_num)) (hk j))
  have hs := CBox.contains_scale hh (if a then 17 else -13) 1000 (by norm_num)
  change (tableAtomBox a kernel).Contains _ at hs
  convert hs using 1
  cases a <;> simp [fullMomentAtom,tableConstant]
lemma fullMoment_contains {a tr : Bool} {m : ℝ} {ell : ℕ} {ab rb : CBox}
    (ha : ab.Contains (fullMomentAtom a tr m ell))
    (hr : rb.Contains (fullMomentRule a tr m ell)) (hm0 : 0 ≤ m) (hm1 : m ≤ 100) :
    (inflate (ab.add rb).re).Contains (fullMoment a tr m ell) := by
  apply inflate_contains (CBox.contains_add ha hr).1
  unfold fullMoment
  have he := (Complex.abs_re_le_norm (fullMomentIntegral a tr m ell-fullMomentRule a tr m ell)).trans_lt
    (fullMoment_error a tr hm0 hm1 ell)
  simpa only [Complex.add_re,Complex.sub_re,add_sub_add_left_eq_sub] using he
lemma fullFactor_step_contains {a b : CBox} {tr : Bool} {m : ℝ} {ell : ℕ} {t : ℝ}
    (ha : a.Contains (fullFactor tr m ell t))
    (hb : b.Contains (Complex.I*Real.pi*(if tr then z t else (t:ℂ)))) :
    ((a.mul b).scale 1 (ell+1)).Contains (fullFactor tr m (ell+1) t) := by
  cases tr
  · change a.Contains (complexDirectFactor m 1 ell t) at ha
    change b.Contains (Complex.I*Real.pi*t) at hb
    change ((a.mul b).scale 1 (ell+1)).Contains (complexDirectFactor m 1 (ell+1) t)
    rw [direct_factor_step]
    exact factor_step_contains ha hb ell
  · change a.Contains (complexTransformedFactor m 1 ell t) at ha
    change b.Contains (Complex.I*Real.pi*z t) at hb
    change ((a.mul b).scale 1 (ell+1)).Contains (complexTransformedFactor m 1 (ell+1) t)
    rw [transformed_factor_step,complexZ_ofReal]
    exact factor_step_contains ha hb ell
end SharpPlanar

end OAI
