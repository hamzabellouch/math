import Mathlib
import OAI.Geometry.PrescribedRicci.UniformFrozenEstimate
import OAI.Geometry.PrescribedPotential.VariablePoisson

namespace OAI

/-! Uniform Local H2. -/

noncomputable section
open Matrix MeasureTheory TemperedDistribution
open scoped ComplexOrder MatrixOrder Matrix.Norms.Elementwise SchwartzMap Real BoundedContinuousFunction
namespace FrozenPoisson
open EllipticKernel SobolevChart
variable {n : ℕ} {ι : Type*} [Fintype ι]

theorem uniform_H2_absorb (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    {M : ℝ} (hM : 0 ≤ M) (hHM : ‖H‖ ≤ M)
    (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ)
    (hsmall : perturbationBound v a * uniformEllipticBound n M ≤ 1/2)
    (u f : L2 (EC n))
    (he : realize 2 u - frozenDifferential H (realize 2 u) -
      (perturbation v a u : 𝓢'(EC n,ℂ)) = (f : 𝓢'(EC n,ℂ))) :
    ‖u‖ ≤ 2*uniformEllipticBound n M*‖f‖ := by
  have he' : shifted H (realize 2 u) =
      ((f+perturbation v a u : L2 (EC n)) : 𝓢'(EC n,ℂ)) := by
    rw [shifted_eq_identity_sub H hH]
    simpa only [← Lp.toTemperedDistributionCLM_apply,map_add] using (sub_eq_iff_eq_add.mp he)
  have hu : u = hilbertResolvent H hH (f+perturbation v a u) := by
    apply realize_injective 2
    have hr := hilbertResolvent_realize H hH 0 (f+perturbation v a u)
    simp only [zero_add] at hr
    have hzero : realize 0 (f+perturbation v a u) = ((f+perturbation v a u : L2 (EC n)) : 𝓢'(EC n,ℂ)) := by
      simp only [realize,neg_zero,besselPotential_zero,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply,Lp.toTemperedDistributionCLM_apply]
    rw [hr,hzero,← he',resolvent_shifted H hH]
  have hC := (uniformEllipticBound_pos (n:=n) hM).le
  have h1 := hilbertResolvent_uniform_bound H hH hM hHM (f+perturbation v a u)
  rw [← hu] at h1
  have h2 := norm_add_le f (perturbation v a u)
  have h3 := perturbation_bound v a u
  have h4 := mul_le_mul_of_nonneg_left (h2.trans (add_le_add_right h3 _)) hC
  have h5 := mul_le_mul_of_nonneg_right hsmall (norm_nonneg u)
  nlinarith only [h1,h4,h5]

end FrozenPoisson

end

end OAI
