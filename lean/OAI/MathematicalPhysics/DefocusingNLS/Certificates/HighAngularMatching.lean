import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HighAngularInitialFlux
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HomotopyCone

namespace OAI

/-! Matched nonzero outgoing jets are incompatible with the high-angular flux sign. -/

namespace DefocusingNLS

theorem highAngular_matched_jets_impossible (qp qm : ℂ) (M : ℕ) (Z : ℝ)
    (hqp : -1 < qp.re) (hqm : -1 < qm.re) (hM : 9 ≤ M)
    (hσp : -(1/32 : ℝ) ≤ 3-(((M : ℂ)+1)/2-qp).re)
    (hσm : -(1/32 : ℝ) ≤ 3-(((M : ℂ)+1)/2-qm).re)
    (hZ : 2704/1000 ≤ Z) (hZ' : Z ≤ 2706/1000)
    (c : ℂ)
    (hH : regularizedSlowSolution qm (M+1) (Complex.I*Z) =
      c*regularizedSlowSolution qp (M+1) (-Complex.I*Z))
    (hD : deriv (regularizedSlowSolution qm (M+1)) (Complex.I*Z) =
      c*deriv (regularizedSlowSolution qp (M+1)) (-Complex.I*Z)) : False := by
  have hpneg := highArcActualFlux_initial_neg qp M Z 1 hqp (Or.inl rfl) hM hσp hZ hZ'
  have hmneg := highArcActualFlux_initial_neg qm M Z (-1) hqm (Or.inr rfl) hM hσm hZ hZ'
  have hp := highArcActualFlux_initial qp M Z 1 hqp (Or.inl rfl) hZ
  have hm := highArcActualFlux_initial qm M Z (-1) hqm (Or.inr rfl) hZ
  dsimp only at hp hm
  simp only [one_mul,Complex.ofReal_neg,mul_neg,neg_mul,neg_neg] at hp hm
  have hG := conjugate_boundary_gauge_normSq M Z
  simp only [neg_mul] at hG hH hD
  rw [hG] at hp
  let K : ℝ := (M : ℝ)-2*Z
  let H := regularizedSlowSolution qm (M+1) (Complex.I*Z)
  let D := deriv (regularizedSlowSolution qm (M+1)) (Complex.I*Z)
  have he : Complex.normSq c*highArcActualFlux qp M Z 1 0+highArcActualFlux qm M Z (-1) 0 =
      Complex.normSq (slowGauge M (Complex.I*Z))*
        (coneForm K (-Complex.I*Z) H D+coneForm K (Complex.I*Z) H D) := by
    dsimp only [K,H,D]
    simp only [neg_mul]
    rw [hp,hm,hH,hD]
    simp only [coneForm_scale]
    ring
  have hsum : coneForm K (-Complex.I*Z) H D+coneForm K (Complex.I*Z) H D =
      K*Complex.normSq H := by
    simp only [coneForm,Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,
      Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im]
    ring
  rw [hsum] at he
  have hK : 0 ≤ K := by
    have hMr : (9 : ℝ) ≤ M := by exact_mod_cast hM
    dsimp [K]
    linarith
  have hnonneg : 0 ≤ Complex.normSq c*highArcActualFlux qp M Z 1 0+
      highArcActualFlux qm M Z (-1) 0 := by
    rw [he]
    exact mul_nonneg (Complex.normSq_nonneg _) (mul_nonneg hK (Complex.normSq_nonneg _))
  have hneg : Complex.normSq c*highArcActualFlux qp M Z 1 0+
      highArcActualFlux qm M Z (-1) 0 < 0 :=
    add_neg_of_nonpos_of_neg
      (mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) hpneg.le) hmneg
  exact (not_lt_of_ge hnonneg) hneg

end DefocusingNLS

end OAI
