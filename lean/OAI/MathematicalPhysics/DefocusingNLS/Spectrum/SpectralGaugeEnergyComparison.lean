import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeCoordinateEnergy

namespace OAI

/-! The fixed-ball norm comparison needs only a positive profile mass and
the uniform profile derivative bound. The angular term is included. -/

namespace DefocusingNLS

theorem spectralGauge_energy_comparison (Q dQ : ℂ) (x dx : ℂ × ℂ) (c D tau : ℝ)
    (hc : 0 < c) (hm : c ≤ ‖Q‖^2) (hdQ : ‖dQ‖ ≤ D) (htau : 0 ≤ tau) :
    let X := (1+tau)*spectralCoordinateEnergy x+spectralCoordinateEnergy dx
    let V := (1+tau)*spectralCoordinateEnergy (spectralGaugeColumns Q x)+
      spectralCoordinateEnergy (spectralGaugeColumns Q dx+spectralGaugeColumns dQ x)
    V ≤ (4+4*D^2/c)*(‖Q‖^2*X) ∧ ‖Q‖^2*X ≤ (1+D^2/c)*V := by
  intro X V
  let K := D^2/c
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hd : ‖dQ‖^2 ≤ D^2 := pow_le_pow_left₀ (norm_nonneg _) hdQ 2
  have hmu : 0 ≤ ‖Q‖^2 := sq_nonneg _
  have hKm : D^2 ≤ K*‖Q‖^2 := by
    calc
      _ = K*c := by dsimp only [K]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hm hK
  have hx := spectralCoordinateEnergy_nonneg x
  have hdx := spectralCoordinateEnergy_nonneg dx
  have hvx := spectralCoordinateEnergy_nonneg (spectralGaugeColumns Q x)
  have hvd := spectralCoordinateEnergy_nonneg (spectralGaugeColumns Q dx+spectralGaugeColumns dQ x)
  have hv := spectralGaugeColumns_energy Q x
  have hupper := spectralGaugeColumns_derivative_upper Q dQ x dx
  have hlower := spectralGaugeColumns_derivative_lower Q dQ x dx
  have hEx : spectralCoordinateEnergy x ≤ X := by dsimp only [X]; nlinarith
  have hprod : ‖dQ‖^2*spectralCoordinateEnergy x ≤ K*‖Q‖^2*X :=
    mul_le_mul (hd.trans hKm) hEx hx (mul_nonneg hK hmu)
  constructor
  · have hcoeff : 4+4*D^2/c = 4+4*K := by dsimp only [K]; ring
    rw [hcoeff]
    have hp : 0 ≤ ‖Q‖^2*((1+tau)*spectralCoordinateEnergy x) := by positivity
    calc
      V ≤ 2*‖Q‖^2*((1+tau)*spectralCoordinateEnergy x)+
          4*‖Q‖^2*spectralCoordinateEnergy dx+4*‖dQ‖^2*spectralCoordinateEnergy x := by
        dsimp only [V]
        rw [hv]
        nlinarith only [hupper]
      _ ≤ 4*(‖Q‖^2*X)+4*‖dQ‖^2*spectralCoordinateEnergy x := by
        dsimp only [X]
        nlinarith only [hp]
      _ ≤ (4+4*K)*(‖Q‖^2*X) := by nlinarith only [hprod]
  · change ‖Q‖^2*X ≤ (1+K)*V
    have hprod' := mul_le_mul_of_nonneg_right (hd.trans hKm) hx
    have hsmall : ‖Q‖^2*spectralCoordinateEnergy dx ≤
        spectralCoordinateEnergy (spectralGaugeColumns Q dx+spectralGaugeColumns dQ x)+
          K*spectralCoordinateEnergy (spectralGaugeColumns Q x) := by
      rw [hv]
      nlinarith only [hlower,hprod']
    have hterm : 0 ≤ K*(tau*spectralCoordinateEnergy (spectralGaugeColumns Q x)) := by positivity
    have hterm' : 0 ≤ K*spectralCoordinateEnergy (spectralGaugeColumns Q dx+spectralGaugeColumns dQ x) :=
      mul_nonneg hK hvd
    have hweight : 0 ≤ (1+tau)*spectralCoordinateEnergy (spectralGaugeColumns Q x) := by positivity
    calc
      ‖Q‖^2*X = (1+tau)/2*spectralCoordinateEnergy (spectralGaugeColumns Q x)+
          ‖Q‖^2*spectralCoordinateEnergy dx := by rw [hv]; dsimp only [X]; ring
      _ ≤ (1+tau)/2*spectralCoordinateEnergy (spectralGaugeColumns Q x)+
          spectralCoordinateEnergy (spectralGaugeColumns Q dx+spectralGaugeColumns dQ x)+
          K*spectralCoordinateEnergy (spectralGaugeColumns Q x) := by linarith only [hsmall]
      _ ≤ (1+K)*V := by
        dsimp only [V]
        nlinarith only [hterm,hterm',hweight]

theorem spectralGauge_weighted_energy_le (Q dQ : ℂ) (x dx : ℂ × ℂ) (c D w v : ℝ)
    (hc : 0 < c) (hm : c ≤ ‖Q‖^2) (hdQ : ‖dQ‖ ≤ D) (hw : 0 ≤ w) (hv : 0 ≤ v) :
    w*‖Q‖^2*(spectralCoordinateEnergy x+spectralCoordinateEnergy dx)+
        v*‖Q‖^2*spectralCoordinateEnergy x ≤
      (1+D^2/c)*(w*(spectralCoordinateEnergy (spectralGaugeColumns Q x)+
        spectralCoordinateEnergy (spectralGaugeColumns Q dx+spectralGaugeColumns dQ x))+
        v*spectralCoordinateEnergy (spectralGaugeColumns Q x)) := by
  have hbase := (spectralGauge_energy_comparison Q dQ x dx c D 0 hc hm hdQ le_rfl).2
  simp only [add_zero,one_mul] at hbase
  have hvalue : ‖Q‖^2*spectralCoordinateEnergy x ≤
      (1+D^2/c)*spectralCoordinateEnergy (spectralGaugeColumns Q x) := by
    rw [spectralGaugeColumns_energy]
    have hp : 0 ≤ ‖Q‖^2*spectralCoordinateEnergy x :=
      mul_nonneg (sq_nonneg _) (spectralCoordinateEnergy_nonneg _)
    have hk : 0 ≤ D^2/c := by positivity
    nlinarith [mul_nonneg hk hp]
  have h1 := mul_le_mul_of_nonneg_left hbase hw
  have h2 := mul_le_mul_of_nonneg_left hvalue hv
  nlinarith only [h1,h2]

end DefocusingNLS

end OAI
