import OAI.MathematicalPhysics.Transonic.Exterior.SourceTrace
import OAI.MathematicalPhysics.Transonic.Exterior.Bound
import OAI.MathematicalPhysics.Transonic.Exterior.BarrierWeights

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates
open FixedInterval ExteriorJet PowerSeries Polynomial Set

structure WindowData where
  amplitude : ℝ
  (root ap : Box)
  (power upper mono rprod : ℕ → Box)
  weights : BarrierWeights
  trace : BarrierTrace.Trace
  poly : ℕ → Box
  (pend zend betaquot crit subsonic : Box)

structure WindowValid (Q : ℤ) (jt : NormalizedTrace.Trace) (sig kap : Box)
    (W : WindowData) : Prop where
  root_pos : 0<W.root.center-W.root.radius
  root_rad : 0≤W.root.radius
  root_lo : (((jt.b 73).center+(jt.b 73).radius:ℤ):ℝ)/Q*
    ((((W.root.center-W.root.radius:ℤ):ℝ)/Q)^73)≤W.amplitude
  root_hi : W.amplitude≤(((jt.b 73).center-(jt.b 73).radius:ℤ):ℝ)/Q*
    ((((W.root.center+W.root.radius:ℤ):ℝ)/Q)^73)
  amplitude_pos : 0<W.amplitude
  ap_holds : Holds Q W.ap W.amplitude
  mono_last : W.mono 73=W.ap
  power_zero : W.power 0=oneBox Q
  power_step : ∀ j, j<73 → W.power (j+1)=mul Q (W.power j) W.root
  upper_eq : ∀ j, 1≤j → j≤73 → W.upper j=mul Q (jt.b j) (W.power j)
  rprod_eq : ∀ j, 2≤j → j≤73 → W.rprod j=mul Q (jt.r j) W.root
  rprod_pos : ∀ j, 2≤j → j≤73 → 0<(W.rprod j).center-(W.rprod j).radius
  mono_step : ∀ j, 1≤j → j<73 → W.mono j=intersect (W.upper j) (divBox Q (W.mono (j+1)) (W.rprod (j+1)))
  signed_zero : W.trace.u 0=zero
  signed_tail : ∀ j, 74≤j → W.trace.u j=zero
  signed_eq : ∀ j, 1≤j → j≤73 → W.trace.u j=signBox j (W.mono j)
  poly_zero : W.poly 0=oneBox Q
  poly_eq : ∀ j, j≠0 → W.poly j=neg (W.trace.u j)
  weights_eq : W.weights=exteriorWeights Q sig kap W.root
  powers : BarrierTrace.ValidPowers Q 8 73 W.trace
  residual_eq : ∀ i, i<220 → W.trace.r i=barrierResidualBox Q W.weights W.trace (i+72)
  panels : ∀ x∈Icc (0:ℝ) 1, ∃ cell rb pb : Box, Holds Q cell x ∧
    rb=hornerBox Q W.trace.r cell 0 220 ∧ pb=hornerBox Q W.poly cell 1 73 ∧
    0<rb.center-rb.radius ∧ 0<pb.center-pb.radius ∧ 5*(pb.center+pb.radius)<Q
  pend_eq : W.pend=hornerBox Q W.poly (oneBox Q) 0 74
  zend_eq : W.zend=add (oneBox Q) (scale 1 256 W.root)
  betaquot_eq : W.betaquot=scale 3 7 (sub (oneBox Q) kap)
  crit_eq : W.crit=add (sub W.pend W.zend)
    (mul Q (mul Q W.betaquot W.zend) (sub (oneBox Q) (mul Q W.pend W.pend)))
  subsonic_eq : W.subsonic=sub (oneBox Q) (mul Q sig (mul Q W.zend W.zend))
  crit_pos : 0<W.crit.center-W.crit.radius
  subsonic_pos : 0<W.subsonic.center-W.subsonic.radius

lemma normalize_window {Q : ℤ} (hQ : 0<Q) (jt : NormalizedTrace.Trace) (sig kap : Box)
    (W : WindowData) (hv : WindowValid Q jt sig kap W)
    (u : PowerSeries ℝ)
    (hb : ∀ j, 1≤j → j≤73 → Holds Q (jt.b j) (PowerSeries.coeff j (scaledReflected u)))
    (hbp : ∀ j, 1≤j → j≤73 → 0<(jt.b j).center-(jt.b j).radius)
    (hr : ∀ j, 2≤j → j≤73 → Holds Q (jt.r j)
      (PowerSeries.coeff j (scaledReflected u)/PowerSeries.coeff (j-1) (scaledReflected u))) :
    ∃ d : ℝ, 0<d ∧ Holds Q W.root d ∧ ∀ j, 1≤j → j≤73 →
      Holds Q (W.mono j) (PowerSeries.coeff j (scaledReflected u)*d^j) := by
  have hp (j:ℕ) (hj:1≤j) (hj':j≤73) : 0<PowerSeries.coeff j (scaledReflected u) :=
    enclosed_pos hQ (hb j hj hj') (hbp j hj hj')
  obtain ⟨d,hd,hde⟩ := ExteriorPolynomial.root_exists _ W.amplitude
    (hp 73 (by norm_num) le_rfl) hv.amplitude_pos
  have hroot := holds_root hQ (hb 73 (by norm_num) le_rfl) (hp 73 (by norm_num) le_rfl)
    hd.le hde hv.root_pos.le hv.root_rad hv.root_lo hv.root_hi
  have hpw := powers_enclosed hQ W.power W.root d hroot hv.power_zero hv.power_step
  have hu : ∀ j, 1≤j → j≤73 → Holds Q (W.upper j) (PowerSeries.coeff j (scaledReflected u)*d^j) := by
    intro j hj hj'
    rw [hv.upper_eq j hj hj']
    exact holds_mul hQ (hb j hj hj') (hpw j hj')
  have hm := normalized_monomials hQ (fun j => PowerSeries.coeff j (scaledReflected u))
    jt.r W.upper W.mono W.rprod d W.root W.ap hroot hu hr
    (fun j hj hj' => ne_of_gt (hp j hj hj')) (ne_of_gt hd) hv.mono_last
    (by rw [hde];exact hv.ap_holds) hv.rprod_eq hv.rprod_pos hv.mono_step
  exact ⟨d,hd,hroot,hm⟩

end SepticProfile.ExteriorCertificates

end
end

end OAI
