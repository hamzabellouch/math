import OAI.Probability.SLE.Loewner.SlitChartBoundaryBasics
import OAI.Probability.SLE.Loewner.InverseDirichletEnergy
import OAI.Probability.SLE.DyadicStrips

namespace OAI

/-! Finite boundary-strip energy for static normalized slit charts. -/
noncomputable section
open Set Filter Metric Function MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma SimpleSlitChart.inverse_strip_dirichlet_finite
    {p : C(unitInterval,ℂ)} (P : SimpleSlitChart p) (x q : ℝ) :
    (∫⁻ z in {z : ℂ | z.re<q ∧ 0<z.im ∧ z.im<Real.pi},
      ENNReal.ofReal (‖deriv (fun w => P.inverse ((x:ℂ)+Complex.exp w)) z‖^2))<∞ := by
  let S : Set ℂ := {z | z.re<q ∧ 0<z.im ∧ z.im<Real.pi}
  let A : ℂ → ℂ := fun z => (x:ℂ)+Complex.exp z
  let f : ℂ → ℂ := fun z => P.inverse (A z)
  have hS : IsOpen S := (isOpen_lt Complex.continuous_re continuous_const).inter
    ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const))
  have hAH : MapsTo A S upperHalfPlane := by
    intro z hz
    change 0<((x:ℂ)+Complex.exp z).im
    have he : 0<(Complex.exp z).im := exp_strip_halfplane hz.2
    simpa only [Complex.add_im,Complex.ofReal_im,zero_add] using he
  have hf : DifferentiableOn ℂ f S := P.inverse_differentiable.comp
    ((differentiable_const (x:ℂ)).add Complex.differentiable_exp).differentiableOn hAH
  have hi : InjOn f S := by
    intro z hz w hw' he
    have hAz := P.right_inverse (A z) (hAH hz)
    have hAw := P.right_inverse (A w) (hAH hw')
    have heA : A z=A w := by
      rw [show P.inverse (A z)=P.inverse (A w) from he,hAw] at hAz
      exact hAz.symm
    exact exp_injective_strip hz.2 hw'.2 (add_left_cancel heA)
  have harea : (∫⁻ z in S, ENNReal.ofReal (‖deriv f z‖^2))=volume (f '' S) := by
    have hd (z : ℂ) (hz : z∈S) :=
      (hf.differentiableAt (hS.mem_nhds hz)).hasDerivAt
    have he := lintegral_abs_det_fderiv_eq_addHaar_image volume hS.measurableSet
      (fun z hz => ((hd z hz).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hi
    simpa only [complex_derivative_real_det,abs_pow,abs_norm] using he
  obtain ⟨M,hM⟩ := P.inverse_bounded_over_ball (‖(x:ℂ)‖+Real.exp q)
  have himage : f '' S ⊆ closedBall (0:ℂ) M := by
    rintro _ ⟨z,hz,rfl⟩
    rw [mem_closedBall,dist_zero_right]
    apply hM (A z) (hAH hz)
    calc
      ‖A z‖ ≤ ‖(x:ℂ)‖+‖Complex.exp z‖ := norm_add_le _ _
      _ ≤ ‖(x:ℂ)‖+Real.exp q := by
        rw [Complex.norm_exp]
        exact add_le_add le_rfl (Real.exp_le_exp.mpr hz.1.le)
  change (∫⁻ z in S, ENNReal.ofReal (‖deriv f z‖^2))<∞
  rw [harea]
  exact (measure_mono himage).trans_lt (isCompact_closedBall (0:ℂ) M).measure_lt_top

end SLEExactGauge

end

end OAI
