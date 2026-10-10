import OAI.MeasureTheory.Falconer.Angular.SphereProduct

namespace OAI

/-! # The four actual radial phases in a far spherical product -/

namespace Falconer

noncomputable def stationaryPhase (t : ℝ) : ℂ := Complex.exp (Complex.I*(t : ℂ))

theorem stationaryPhase_star (t : ℝ) : star (stationaryPhase t) = stationaryPhase (-t) := by
  change (starRingEnd ℂ) (Complex.exp (Complex.I*(t : ℂ))) = _
  rw [← Complex.exp_conj]
  simp only [stationaryPhase,map_mul,Complex.conj_I,Complex.conj_ofReal,Complex.ofReal_neg]
  congr 1
  ring

theorem stationaryPhase_mul (s t : ℝ) :
    stationaryPhase s*stationaryPhase t = stationaryPhase (s+t) := by
  rw [stationaryPhase,stationaryPhase,← Complex.exp_add,stationaryPhase]
  congr 1
  push_cast
  ring

theorem stationary_four_phase_product (s t : ℝ) (A B C D : ℂ) :
    (stationaryPhase s*A+star (stationaryPhase s*B))*
      star (stationaryPhase t*C+star (stationaryPhase t*D)) =
      stationaryPhase (s-t)*(A*star C)+
      stationaryPhase (s+t)*(A*D)+
      stationaryPhase (-s-t)*(star B*star C)+
      stationaryPhase (t-s)*(star B*D) := by
  calc
    _ = (stationaryPhase s*stationaryPhase (-t))*(A*star C)+
        (stationaryPhase s*stationaryPhase t)*(A*D)+
        (stationaryPhase (-s)*stationaryPhase (-t))*(star B*star C)+
        (stationaryPhase t*stationaryPhase (-s))*(star B*D) := by
      simp only [star_add,star_mul',star_star,stationaryPhase_star]
      ring_nf
    _ = _ := by
      simp only [stationaryPhase_mul,sub_eq_add_neg]

theorem stationarySphereApprox_four_phases (m J : ℕ) (s t : ℝ)
    (B C : Space (m+3) → ℂ) (e f : Sphere (m+3)) :
    stationarySphereApprox m J s B e*star (stationarySphereApprox m J t C f) =
      ((s^(-(((m+2 : ℕ) : ℝ)/2))*t^(-(((m+2 : ℕ) : ℝ)/2)) : ℝ) : ℂ)*
      (stationaryPhase (s-t)*(directStationarySum m J s B e*star (directStationarySum m J t C f))+
        stationaryPhase (s+t)*(directStationarySum m J s B e*
          directStationarySum m J t (antipodalConjugate C) f)+
        stationaryPhase (-s-t)*(star (directStationarySum m J s (antipodalConjugate B) e)*
          star (directStationarySum m J t C f))+
        stationaryPhase (t-s)*(star (directStationarySum m J s (antipodalConjugate B) e)*
          directStationarySum m J t (antipodalConjugate C) f)) := by
  have h := stationary_four_phase_product s t
    (directStationarySum m J s B e) (directStationarySum m J s (antipodalConjugate B) e)
    (directStationarySum m J t C f) (directStationarySum m J t (antipodalConjugate C) f)
  change _ = _*_
  rw [← h]
  simp only [stationarySphereApprox,stationaryPhase,star_mul',Complex.ofReal_mul]
  have ht : star (((t^(-(((m+2 : ℕ) : ℝ)/2))) : ℝ) : ℂ) =
      (((t^(-(((m+2 : ℕ) : ℝ)/2))) : ℝ) : ℂ) := by
    change (starRingEnd ℂ) _ = _
    exact Complex.conj_ofReal _
  rw [ht]
  ring

end Falconer

end OAI
