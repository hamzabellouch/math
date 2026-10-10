import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialIntegralConvergence
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressurePrimitive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace OAI

/-! Uniform convergence of radial primitives implies convergence against C1 test functions. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem radial_primitive_test_convergence (R : ℝ) (hR : 0 ≤ R)
    (f : ℕ → ℝ → ℝ) (hf : ∀ n, Continuous (f n)) (F : ℝ → ℝ)
    (hF : ContinuousOn F (Icc 0 R))
    (hT : TendstoUniformlyOn (fun n r => ∫ t in (0 : ℝ)..r, f n t) F atTop (Icc 0 R))
    (φ ψ : ℝ → ℝ) (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφD : ∀ r ∈ Ioo 0 R, HasDerivAt φ (ψ r) r) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..R, φ t*f n t) atTop
      (𝓝 (φ R*F R-φ 0*F 0-∫ t in (0 : ℝ)..R, ψ t*F t)) := by
  let Fn := fun n r => ∫ t in (0 : ℝ)..r, f n t
  have hFnD (n : ℕ) (r : ℝ) : HasDerivAt (Fn n) (f n r) r :=
    ((hf n).integral_hasStrictDerivAt 0 r).hasDerivAt
  have hFnC (n : ℕ) : Continuous (Fn n) :=
    (show Differentiable ℝ (Fn n) from fun r => (hFnD n r).differentiableAt).continuous
  have hψT : TendstoUniformlyOn (fun _ : ℕ => ψ) ψ atTop (Icc 0 R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall (fun _ _ _ => by simpa only [dist_self] using hε)
  have hprod := radial_uniform_product R (fun _ => ψ) Fn ψ F hψT hT hψ.continuousOn hF
  have hI := radial_integral_tendsto R hR (fun n r => ψ r*Fn n r) (fun r => ψ r*F r)
    (fun n => (hψ.mul (hFnC n)).continuousOn) (hψ.continuousOn.mul hF) hprod
  have h0 := hT.tendsto_at (show (0 : ℝ) ∈ Icc 0 R from ⟨le_rfl,hR⟩)
  have hR' := hT.tendsto_at (show R ∈ Icc 0 R from ⟨hR,le_rfl⟩)
  have hout := ((hR'.const_mul (φ R)).sub (h0.const_mul (φ 0))).sub hI
  have he (n : ℕ) : (∫ t in (0 : ℝ)..R, φ t*f n t)=
      φ R*Fn n R-φ 0*Fn n 0-∫ t in (0 : ℝ)..R, ψ t*Fn n t := by
    apply intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    · simpa only [uIcc_of_le hR] using hφ.continuousOn (s := Icc 0 R)
    · simpa only [uIcc_of_le hR] using (hFnC n).continuousOn (s := Icc 0 R)
    · intro r hr
      exact hφD r (by simpa only [min_eq_left hR,max_eq_right hR] using hr)
    · intro r _
      exact hFnD n r
    · exact hψ.intervalIntegrable 0 R
    · exact (hf n).intervalIntegrable 0 R
  exact hout.congr' (Eventually.of_forall (fun n => (he n).symm))

end DefocusingNLS

end OAI
