import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCoupledParameterLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialAverageUniform
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressurePrimitive

namespace OAI

/-! Fixed-power parameter continuity of the actual inner radial derivative. -/

open Set Filter
namespace DefocusingNLS

theorem radial_uniform_fixed_power (R : ℝ) (Hn : ℕ → ℝ → ℝ) (H : ℝ → ℝ)
    (hH : ContinuousOn H (Icc 0 R)) (ht : TendstoUniformlyOn Hn H atTop (Icc 0 R))
    (p : ℕ) : TendstoUniformlyOn (fun i r => (Hn i r)^p) (fun r => (H r)^p) atTop (Icc 0 R) := by
  induction p with
  | zero =>
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall (fun _ _ _ => by simpa only [pow_zero,dist_self] using hε)
  | succ p ih =>
    simpa only [pow_succ] using radial_uniform_product R _ _ _ _ ih ht (hH.pow p) hH

theorem radial_coupled_derivative_parameter_limit (P : RadialInnerData) (Pn : ℕ → RadialInnerData)
    (hp : ∀ i, (Pn i).p=P.p) (hR : ∀ i, (Pn i).R=P.R)
    (hlo : Tendsto (fun i => (Pn i).lo) atTop (nhds P.lo))
    (hc : Tendsto (fun i => (Pn i).c) atTop (nhds P.c))
    (hb : Tendsto (fun i => (Pn i).b) atTop (nhds P.b))
    (H : ℝ → ℝ) (Hn : ℕ → ℝ → ℝ)
    (hH : RadialInnerOutputSpec P.p P.R P.lo P.c P.b H H)
    (hHn : ∀ i, RadialInnerOutputSpec (Pn i).p (Pn i).R (Pn i).lo (Pn i).c (Pn i).b (Hn i) (Hn i)) :
    TendstoUniformlyOn (fun i => deriv (Hn i)) (deriv H) atTop (Icc 0 P.R) := by
  have hA := radial_coupled_parameter_limit P Pn hp hR hlo hc hb H Hn hH hHn
  have hHI : ∀ r ∈ Icc 0 P.R, H r ∈ Icc (999/1000 : ℝ) 1 :=
    fun r hr => ⟨P.lo_lower.trans (hH.2.2.2.2.1 r hr).1.1,(hH.2.2.2.2.1 r hr).1.2⟩
  have hHnI : ∀ i r, r ∈ Icc 0 P.R → Hn i r ∈ Icc (999/1000 : ℝ) 1 := by
    intro i r hr
    have hr' : r ∈ Icc 0 (Pn i).R := by simpa only [hR i] using hr
    exact ⟨(Pn i).lo_lower.trans ((hHn i).2.2.2.2.1 r hr').1.1,
      ((hHn i).2.2.2.2.1 r hr').1.2⟩
  have hV := radialAmplitudePotential_uniform_convergence P.R P.hR2
    (fun i => (Pn i).c) (fun i => (Pn i).b) P.c P.b (fun i => (Pn i).hc) P.hc hc hb
    Hn H (fun i => (hHn i).1.continuous) hH.1.continuous hHnI hHI hA
  have hVC := continuousOn_radialAmplitudePotential P.c P.b P.R H hH.1.continuous
    (fun r hr => ne_of_gt (lt_of_lt_of_le (by norm_num) (hHI r hr).1))
  have hVnC (i : ℕ) := continuousOn_radialAmplitudePotential (Pn i).c (Pn i).b P.R
    (Hn i) (hHn i).1.continuous
    (fun r hr => ne_of_gt (lt_of_lt_of_le (by norm_num) (hHnI i r hr).1))
  have hF := (radial_uniform_fixed_power P.R Hn H hH.1.continuous.continuousOn hA P.p).sub
    (radial_uniform_product P.R _ Hn _ H hV hA hVC hH.1.continuous.continuousOn)
  have hAvg := radial_derivative_integral_uniform P.R (by linarith [P.hR])
    (fun i r => (Hn i r)^P.p-radialAmplitudePotential (Pn i).c (Pn i).b (Hn i) r*Hn i r)
    (fun r => (H r)^P.p-radialAmplitudePotential P.c P.b H r*H r)
    (fun i => ((hHn i).1.continuous.pow P.p).continuousOn.sub
      ((hVnC i).mul (hHn i).1.continuous.continuousOn))
    ((hH.1.continuous.pow P.p).continuousOn.sub (hVC.mul hH.1.continuous.continuousOn)) hF
  apply (hAvg.congr ?_).congr_right
  · intro r hr
    exact (radial_inner_integral_formula P H hH r hr).symm
  · exact Eventually.of_forall (fun i r hr => by
      have hr' : r ∈ Icc 0 (Pn i).R := by simpa only [hR i] using hr
      simpa only [hp i] using (radial_inner_integral_formula (Pn i) (Hn i) (hHn i) r hr').symm)

end DefocusingNLS

end OAI
