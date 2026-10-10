import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPhaseConvergence
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPolarJet
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

namespace OAI

/-! Uniform convergence of the actual complex amplitude-phase jets. -/

open Set Filter Topology
namespace DefocusingNLS

theorem radial_uniform_complex_product (R : ℝ) (f g : ℕ → ℝ → ℂ) (F G : ℝ → ℂ)
    (hf : TendstoUniformlyOn f F atTop (Icc 0 R))
    (hg : TendstoUniformlyOn g G atTop (Icc 0 R))
    (hF : ContinuousOn F (Icc 0 R)) (hG : ContinuousOn G (Icc 0 R)) :
    TendstoUniformlyOn (fun n r => f n r*g n r) (fun r => F r*G r) atTop (Icc 0 R) := by
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).mp
    (hf.tendstoLocallyUniformlyOn.mul₀ hg.tendstoLocallyUniformlyOn hF hG)

theorem radial_uniform_ofReal {s : Set ℝ} (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ)
    (h : TendstoUniformlyOn f F atTop s) :
    TendstoUniformlyOn (fun n r => (f n r : ℂ)) (fun r => (F r : ℂ)) atTop s := by
  exact Complex.isometry_ofReal.uniformContinuous.comp_tendstoUniformlyOn h

theorem radial_uniform_phase_exp {s : Set ℝ} (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ)
    (h : TendstoUniformlyOn f F atTop s) :
    TendstoUniformlyOn (fun n r => Complex.exp (Complex.I*(f n r : ℂ)))
      (fun r => Complex.exp (Complex.I*(F r : ℂ))) atTop s := by
  have hi : Isometry (fun t : ℝ => Complex.I*(t : ℂ)) := by
    rw [isometry_iff_dist_eq]
    intro x y
    simp only [dist_eq_norm,← mul_sub,← Complex.ofReal_sub,norm_mul,Complex.norm_I,
      one_mul,Complex.norm_real,Real.norm_eq_abs]
  exact UniformContinuousOn.comp_tendstoUniformlyOn_eventually
    (Eventually.of_forall (fun _ _ _ => by simp)) (fun _ _ => by simp)
    (UniformContinuousOn.cexp 0) (hi.uniformContinuous.comp_tendstoUniformlyOn h)

theorem radial_polar_jet_uniform (R : ℝ) (H J v φ : ℕ → ℝ → ℝ) (A D w ψ : ℝ → ℝ)
    (hA : Continuous A) (hD : Continuous D) (hw : ContinuousOn w (Icc 0 R)) (hψ : Continuous ψ)
    (hH : TendstoUniformlyOn H A atTop (Icc 0 R))
    (hJ : TendstoUniformlyOn J D atTop (Icc 0 R))
    (hv : TendstoUniformlyOn v w atTop (Icc 0 R))
    (hφ : TendstoUniformlyOn φ ψ atTop (Icc 0 R)) :
    TendstoUniformlyOn (fun n => radialPolar (H n) (φ n)) (radialPolar A ψ) atTop (Icc 0 R) ∧
    TendstoUniformlyOn (fun n => radialPolarSlope (H n) (J n) (v n) (φ n))
      (radialPolarSlope A D w ψ) atTop (Icc 0 R) := by
  have he := radial_uniform_phase_exp φ ψ hφ
  have hEc : Continuous (fun r => Complex.exp (Complex.I*(ψ r : ℂ))) := by fun_prop
  have hAc : Continuous (fun r => (A r : ℂ)) := Complex.continuous_ofReal.comp hA
  have hDc : Continuous (fun r => (D r : ℂ)) := Complex.continuous_ofReal.comp hD
  have hwc : ContinuousOn (fun r => (w r : ℂ)) (Icc 0 R) := Complex.continuous_ofReal.comp_continuousOn hw
  have hI : TendstoUniformlyOn (fun _ : ℕ => fun _ : ℝ => Complex.I) (fun _ => Complex.I)
      atTop (Icc 0 R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    exact fun ε hε => Eventually.of_forall (fun _ _ _ => by simpa only [dist_self] using hε)
  have hIA := radial_uniform_complex_product R _ _ _ _ hI (radial_uniform_ofReal H A hH)
    continuousOn_const hAc.continuousOn
  have hIAw := radial_uniform_complex_product R _ _ _ _ hIA (radial_uniform_ofReal v w hv)
    (continuous_const.mul hAc).continuousOn hwc
  exact ⟨radial_uniform_complex_product R _ _ _ _ (radial_uniform_ofReal H A hH) he
      hAc.continuousOn hEc.continuousOn,
    radial_uniform_complex_product R _ _ _ _ ((radial_uniform_ofReal J D hJ).add hIAw) he
      (hDc.continuousOn.add ((continuous_const.mul hAc).continuousOn.mul hwc)) hEc.continuousOn⟩

end DefocusingNLS

end OAI
