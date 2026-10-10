import Mathlib
import OAI.Analysis.AffineBernstein.ProjectiveHemisphere

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open intervalIntegral

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/- The projective hemisphere formula for an arbitrary measurable integrand,
with the normalization map written explicitly. -/
theorem projective_hemisphere_normalized_lintegral
    (g : WithLp 2 (F × ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1,
      if 0 < (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 then g e else 0 ∂volume.toSphere) =
    ∫⁻ x : F, ENNReal.ofReal (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ ^
      (Module.finrank ℝ F+1)) *
      g (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ • WithLp.toLp 2 (x,(1:ℝ))) := by
  let f : WithLp 2 (F × ℝ) → ℝ≥0∞ := fun y => g (‖y‖⁻¹ • y)
  have hf : Measurable f := hg.comp (by fun_prop)
  have hscale (y : WithLp 2 (F × ℝ)) (t : ℝ) (ht : 0 < t) : f (t • y) = f y := by
    dsimp [f]
    congr 1
    rw [norm_smul,Real.norm_of_nonneg ht.le,mul_inv_rev,smul_smul]
    congr 1
    rw [mul_assoc,inv_mul_cancel₀ ht.ne',mul_one]
  have h := projective_hemisphere_lintegral f hf hscale
  have hs (e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1) : f e = g e := by
    have he : ‖(e:WithLp 2 (F × ℝ))‖ = 1 := by
      exact norm_eq_of_mem_sphere e
    simp [f,he]
  simp_rw [hs] at h
  exact h

/- Substitution of a pointwise density identity into the exact hemisphere
formula. The density law need only hold on this chart, and the tangent space
may be zero-dimensional. -/
theorem projective_hemisphere_density_lintegral
    (g : WithLp 2 (F × ℝ) → ℝ≥0∞) (hg : Measurable g) (d : F → ℝ≥0∞)
    (hd : ∀ x : F, d x = ENNReal.ofReal (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ ^
      (Module.finrank ℝ F+1)) *
      g (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ • WithLp.toLp 2 (x,(1:ℝ)))) :
    (∫⁻ e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1,
      if 0 < (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 then g e else 0 ∂volume.toSphere) =
      ∫⁻ x : F, d x := by
  rw [projective_hemisphere_normalized_lintegral g hg]
  exact lintegral_congr (fun x => (hd x).symm)

end AffineBernstein
end

end OAI
