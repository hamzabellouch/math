import Mathlib
import OAI.Analysis.AffineBernstein.LinearSphere

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
section DependencyScope
open Filter
open scoped Topology

section HomogeneousSphere
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/- The projective sphere Jacobian cancels a homogeneous density of degree
`-(dim E - 1)`, leaving precisely one inverse norm. -/
lemma sphere_lintegral_homogeneous_linear (μ : Measure E) [μ.IsAddHaarMeasure]
    (A : E ≃L[ℝ] E) (f : E → ℝ≥0∞) (hf : Measurable f)
    (hscale : ∀ (x : E), x ≠ 0 → ∀ (r : ℝ), 0 < r →
      f (r • x) = ENNReal.ofReal ((r⁻¹)^(Module.finrank ℝ E - 1)) * f x) :
    (∫⁻ e : Metric.sphere (0:E) 1, f e ∂μ.toSphere) =
      ENNReal.ofReal |A.toLinearMap.det| *
        ∫⁻ e : Metric.sphere (0:E) 1,
          f (A e) * ENNReal.ofReal (‖A e‖⁻¹) ∂μ.toSphere := by
  let g : E → ℝ≥0∞ := fun x => f (‖x‖⁻¹ • x)
  have hg : Measurable g := hf.comp (measurable_norm.inv.smul measurable_id)
  have hgscale (x : E) (r : ℝ) (hr : 0 < r) : g (r • x) = g x := by
    dsimp [g]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,mul_inv_rev,smul_smul]
    congr 2
    field_simp
  have htrans := sphere_lintegral_linear_jacobian μ A g hg hgscale
  have hn (e : Metric.sphere (0:E) 1) : ‖(e:E)‖ = 1 := by
    simp
  have hgs (e : Metric.sphere (0:E) 1) : g e = f e := by simp [g,hn]
  have heq (e : Metric.sphere (0:E) 1) :
      g (A e) * ENNReal.ofReal (‖A e‖⁻¹ ^ Module.finrank ℝ E) =
        f (A e) * ENNReal.ofReal (‖A e‖⁻¹) := by
    have he : (e:E) ≠ 0 := by intro h; simpa [h] using hn e
    have ha : 0 < ‖A e‖ := norm_pos_iff.mpr (fun h => he (A.injective (by simpa using h)))
    dsimp [g]
    rw [hscale (A e) (norm_ne_zero_iff.mp ha.ne') _ (inv_pos.mpr ha),inv_inv]
    have hp : ‖A e‖ ^ (Module.finrank ℝ E - 1) *
        (‖A e‖⁻¹ ^ Module.finrank ℝ E) = ‖A e‖⁻¹ := by
      have hd := Nat.sub_add_cancel (Module.finrank_pos (R:=ℝ) (M:=E))
      conv_lhs => arg 2; rw [← hd,pow_succ]
      rw [← mul_assoc,← mul_pow,mul_inv_cancel₀ ha.ne',one_pow,one_mul]
    calc
      _ = f (A e) * (ENNReal.ofReal (‖A e‖ ^ (Module.finrank ℝ E - 1)) *
        ENNReal.ofReal (‖A e‖⁻¹ ^ Module.finrank ℝ E)) := by ring
      _ = _ := by rw [← ENNReal.ofReal_mul (pow_nonneg (norm_nonneg _) _),hp]
  simpa only [hgs,heq] using htrans
end HomogeneousSphere



end DependencyScope
end AffineBernstein
end

end OAI
