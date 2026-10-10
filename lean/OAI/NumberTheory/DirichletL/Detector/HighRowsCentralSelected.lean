import OAI.NumberTheory.DirichletL.Detector.HighRowsCentralError

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ProbeLocal

lemma unramifiedSelected_central_error (Q a e : ℝ) (A eta v x w z : ℂ)
    (hQ : 4≤Q) (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hA : ‖A‖≤1) (heta : ‖eta‖=1) (hv : ‖v‖=1)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    ‖unramifiedSelected Q A eta v x w z+unramifiedClosed Q A eta v x w z*star v‖≤
      720*Q^(-(51/100:ℝ)) := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  have hL : 1≤Q^(6*e) := Real.one_le_rpow hQ1 (by positivity)
  have hV : ‖coordV Q z‖≤1/2 := by
    rw [coordV_norm Q hQ0]
    exact rpow_le_half Q _ hQ (by rw [hz];norm_num)
  have hD : ‖coordD Q eta v x‖≤1/2 :=
    (coordD_norm_le Q hQ0 eta v x heta.le hv.le).trans
      (rpow_le_half Q _ hQ (by rw [hx];linarith))
  have hW : ‖coordW Q v w‖≤Q^(6*e) := (coordW_norm_le Q hQ0 v w hv.le).trans
    (Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hw];linarith))
  have hq : ‖(Q:ℂ)^(-w)‖≤Q^(6*e) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hw];linarith)
  obtain ⟨hVT,hDT,hET,hBET⟩ := central_unramified_error_weights Q a e A eta v x w z
    hQ ha ha1 he he1 hA heta.le hv.le hx hw hz
  have hi := selected_phase_identities Q eta v x w hQ0 heta hv
  have hh := central_phase_error_bound (coordV Q z) (coordW Q v w) (coordD Q eta v x)
    (unramifiedMarked Q A eta v x w z) (star eta*(Q:ℂ)^x) ((Q:ℂ)^(-w)) (star v)
    (Q^(6*e)) (Q^(-(51/100:ℝ))) hL hV hD hW hq (by rw [norm_star,hv])
    hVT hDT hET hBET hi.1 hi.2
  simpa only [unramifiedSelected,unramifiedClosed,unramifiedMarked] using hh

end SevenEighths.ProbeEuler
end

end OAI
