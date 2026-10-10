import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCoupledDerivativeParameter
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPhaseConvergence
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPolarJet

namespace OAI

/-! Continuity of the actual complex inner boundary jet at a fixed power. -/

open Set Filter
namespace DefocusingNLS

theorem radial_coupled_polar_deriv (P : RadialInnerData) (H : ℝ → ℝ)
    (hH : RadialInnerOutputSpec P.p P.R P.lo P.c P.b H H) (r : ℝ) (hr : r ∈ Icc 0 P.R) :
    deriv (radialPolar H (radialPhase P.c (radialClampedAmplitude P.R H))) r=
      radialPolarSlope H (deriv H) (radialPhaseSpeed P.c H)
        (radialPhase P.c (radialClampedAmplitude P.R H)) r := by
  have hC := radialClampedAmplitude_continuous P.R H hH.1.continuous
  have hn : ∀ t, radialClampedAmplitude P.R H t ≠ 0 := by
    intro t
    have hi := (hH.2.2.2.2.1 (radialClamp P.R t)
      (radialClamp_mem P.R t (by linarith [P.hR]))).1.1
    change H (radialClamp P.R t) ≠ 0
    linarith [P.lo_lower]
  have hph := radialPhase_differentiable P.c _ hC hn
  have hdph := (radialPhase_hasDerivAt P.c _ hC hn r).deriv
  rw [radialVelocity_clamped_eq P.c P.R H r hr] at hdph
  rw [(radialPolar_hasDerivAt H _ hH.1 hph r).deriv,hdph]
  rfl

theorem radial_coupled_complex_parameter_limit (P : RadialInnerData) (Pn : ℕ → RadialInnerData)
    (hp : ∀ i, (Pn i).p=P.p) (hR : ∀ i, (Pn i).R=P.R)
    (hlo : Tendsto (fun i => (Pn i).lo) atTop (nhds P.lo))
    (hc : Tendsto (fun i => (Pn i).c) atTop (nhds P.c))
    (hb : Tendsto (fun i => (Pn i).b) atTop (nhds P.b))
    (H : ℝ → ℝ) (Hn : ℕ → ℝ → ℝ)
    (hH : RadialInnerOutputSpec P.p P.R P.lo P.c P.b H H)
    (hHn : ∀ i, RadialInnerOutputSpec (Pn i).p (Pn i).R (Pn i).lo (Pn i).c (Pn i).b (Hn i) (Hn i)) :
    Tendsto (fun i =>
      let Q := radialPolar (Hn i) (radialPhase (Pn i).c (radialClampedAmplitude P.R (Hn i)))
      (Q P.R,deriv Q P.R)) atTop
      (nhds (radialPolar H (radialPhase P.c (radialClampedAmplitude P.R H)) P.R,
        deriv (radialPolar H (radialPhase P.c (radialClampedAmplitude P.R H))) P.R)) := by
  have hA := radial_coupled_parameter_limit P Pn hp hR hlo hc hb H Hn hH hHn
  have hD := radial_coupled_derivative_parameter_limit P Pn hp hR hlo hc hb H Hn hH hHn
  have hHI : ∀ r ∈ Icc 0 P.R, H r ∈ Icc (999/1000 : ℝ) 1 :=
    fun r hr => ⟨P.lo_lower.trans (hH.2.2.2.2.1 r hr).1.1,(hH.2.2.2.2.1 r hr).1.2⟩
  have hHnI : ∀ i r, r ∈ Icc 0 P.R → Hn i r ∈ Icc (999/1000 : ℝ) 1 := by
    intro i r hr
    have hr' : r ∈ Icc 0 (Pn i).R := by simpa only [hR i] using hr
    exact ⟨(Pn i).lo_lower.trans ((hHn i).2.2.2.2.1 r hr').1.1,
      ((hHn i).2.2.2.2.1 r hr').1.2⟩
  have hv := radial_phase_speed_uniform P.R (fun i => (Pn i).c) P.c
    (fun i => (Pn i).hc) hc Hn H (fun i => (hHn i).1.continuous) hH.1.continuous hHnI hHI hA
  have hφ := radial_phase_clamped_uniform P.R (by linarith [P.hR]) (fun i => (Pn i).c) P.c
    (fun i => (Pn i).hc) hc Hn H (fun i => (hHn i).1.continuous) hH.1.continuous hHnI hHI hA
  have hr : P.R ∈ Icc 0 P.R := ⟨by linarith [P.hR],le_rfl⟩
  let J : ℝ × ℝ × ℝ × ℝ → ℂ × ℂ := fun z =>
    ((z.1 : ℂ)*Complex.exp (Complex.I*(z.2.2.2 : ℂ)),
      ((z.2.1 : ℂ)+Complex.I*(z.1 : ℂ)*(z.2.2.1 : ℂ))*Complex.exp (Complex.I*(z.2.2.2 : ℂ)))
  have hJ : Continuous J := by dsimp [J]; fun_prop
  have hh := hJ.continuousAt.tendsto.comp
    ((hA.tendsto_at hr).prodMk_nhds ((hD.tendsto_at hr).prodMk_nhds
      ((hv.tendsto_at hr).prodMk_nhds (hφ.tendsto_at hr))))
  have hdn (i : ℕ) : deriv (radialPolar (Hn i)
      (radialPhase (Pn i).c (radialClampedAmplitude P.R (Hn i)))) P.R=
      radialPolarSlope (Hn i) (deriv (Hn i)) (radialPhaseSpeed (Pn i).c (Hn i))
        (radialPhase (Pn i).c (radialClampedAmplitude P.R (Hn i))) P.R := by
    simpa only [hR i] using radial_coupled_polar_deriv (Pn i) (Hn i) (hHn i) P.R
      (by simpa only [hR i] using hr)
  dsimp only
  simp only [hdn,radial_coupled_polar_deriv P H hH P.R hr]
  simpa only [J,radialPolar,radialPolarSlope] using! hh

end DefocusingNLS

end OAI
