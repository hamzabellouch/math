import OAI.NumberTheory.DirichletL.Detector.HighRowsCentralSelected

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma unramifiedClosed_central_lower (Q a e : ℝ) (A eta v x w z : ℂ)
    (hQ : 480≤Q) (ha : (51/100:ℝ)≤a) (ha1 : a≤1)
    (he : 0<e) (he1 : e≤1/1000) (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    1/2≤‖unramifiedClosed Q A eta v x w z‖ := by
  have hQ0 : 0<Q := by linarith
  have hd := unramifiedClosed_first_region_bound Q A eta v x w z (10*e)
    (by linarith) hA heta hv (by positivity) (by rw [hx];linarith)
    (by rw [hz]) (by rw [hw];linarith) (by rw [hx,hw];linarith)
  have hp : Q^(-1-min (10*e) (1/50:ℝ))≤Q^(-1:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by
      have hm : 0≤min (10*e) (1/50:ℝ) := by positivity
      linarith)
  have hi : Q^(-1:ℝ)≤1/480 := by
    rw [Real.rpow_neg_one,←one_div]
    exact one_div_le_one_div_of_le (by norm_num) hQ
  have ht := norm_sub_le (1:ℂ) (unramifiedClosed Q A eta v x w z)
  have ht' := norm_add_le (1-unramifiedClosed Q A eta v x w z)
    (unramifiedClosed Q A eta v x w z)
  rw [sub_add_cancel,norm_one,norm_sub_rev] at ht'
  nlinarith

lemma unramifiedSelected_central_quotient (Q a e : ℝ) (A eta v x w z : ℂ)
    (hQ : 480≤Q) (ha : (51/100:ℝ)≤a) (ha1 : a≤1)
    (he : 0<e) (he1 : e≤1/1000) (hA : ‖A‖≤1) (heta : ‖eta‖=1) (hv : ‖v‖=1)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    ‖unramifiedSelected Q A eta v x w z/unramifiedClosed Q A eta v x w z+star v‖≤
      1440*Q^(-(51/100:ℝ)) := by
  have hh := unramifiedClosed_central_lower Q a e A eta v x w z hQ ha ha1 he he1 hA heta.le hv.le hx hw hz
  have hn : unramifiedClosed Q A eta v x w z≠0 := by
    intro hz;rw [hz,norm_zero] at hh;norm_num at hh
  have hp : 0<‖unramifiedClosed Q A eta v x w z‖ := by linarith
  have hb := unramifiedSelected_central_error Q a e A eta v x w z
    (by linarith) ha ha1 he he1 hA heta hv hx hw hz
  have hid : unramifiedSelected Q A eta v x w z/unramifiedClosed Q A eta v x w z+star v=
      (unramifiedSelected Q A eta v x w z+unramifiedClosed Q A eta v x w z*star v)/
      unramifiedClosed Q A eta v x w z := by field_simp
  rw [hid,norm_div]
  apply (div_le_iff₀ hp).mpr
  have ht : 0≤Q^(-(51/100:ℝ)) := Real.rpow_nonneg (by linarith) _
  nlinarith
end SevenEighths.ProbeEuler
end

end OAI
