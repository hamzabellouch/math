import Mathlib
import OAI.Geometry.PrescribedRicci.KahlerEnergyChain
import OAI.Geometry.PrescribedRicci.KaehlerTrace

namespace OAI

/-! Kaehler Log Trace. -/

section

 
noncomputable section
open Matrix Filter Set Topology
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ}

lemma holRealDeriv_log {φ : Coordinates d → ℝ} {z : Coordinates d}
    (hφ : DifferentiableAt ℝ φ z) (hp : φ z ≠ 0) (a : Fin d) :
    holRealDeriv (fun y => Real.log (φ y)) z a =
      ((φ z)⁻¹:ℝ) * holRealDeriv φ z a := by
  have he := congrFun (holRealDeriv_comp hφ (Real.differentiableAt_log hp)) a
  simpa only [Function.comp_def,Real.deriv_log] using he

lemma holRealDeriv_inv {φ : Coordinates d → ℝ} {z : Coordinates d}
    (hφ : DifferentiableAt ℝ φ z) (hp : φ z ≠ 0) (a : Fin d) :
    holRealDeriv (fun y => (φ y)⁻¹) z a =
      (-((φ z)^2)⁻¹:ℝ) * holRealDeriv φ z a := by
  have he := congrFun (holRealDeriv_comp hφ (differentiableAt_inv hp)) a
  simpa only [Function.comp_def,deriv_inv] using he

lemma potentialMatrix_log {φ : Coordinates d → ℝ} {z : Coordinates d}
    (hφ : ContDiffAt ℝ ∞ φ z) (hp : φ z ≠ 0) (b a : Fin d) :
    PotentialKaehler.potentialMatrix (fun y => Real.log (φ y)) z b a =
      ((φ z)⁻¹:ℝ)*PotentialKaehler.potentialMatrix φ z b a -
        (((φ z)^2)⁻¹:ℝ)*star (holRealDeriv φ z b)*holRealDeriv φ z a := by
  rw [← barDeriv_holRealDeriv (hφ.log hp)]
  have he : (fun y => holRealDeriv (fun w => Real.log (φ w)) y a) =ᶠ[nhds z]
      (fun y => (((φ y)⁻¹:ℝ):ℂ)*holRealDeriv φ y a) := by
    filter_upwards [(hφ.of_le (show (1:ℕ∞ω) ≤ ∞ by simp)).eventually (by simp),
      hφ.continuousAt.eventually (eventually_ne_nhds hp)] with y hy hn
    exact holRealDeriv_log (hy.differentiableAt (by simp)) hn a
  have hd := hφ.differentiableAt (by simp)
  have hi : DifferentiableAt ℝ (fun y => (φ y)⁻¹) z := hd.inv hp
  have hic : DifferentiableAt ℝ (fun y => (((φ y)⁻¹:ℝ):ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z hi
  rw [barDeriv_congr he,barDeriv_mul hic
      ((contDiffAt_holRealDeriv hφ a).differentiableAt (by simp)),
    barDeriv_ofReal hi,barDeriv_holRealDeriv hφ,holRealDeriv_inv hd hp]
  simp only [star_mul,Complex.star_def,Complex.ofReal_neg,map_neg,Complex.conj_ofReal]
  ring

variable {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

def logTrace (h g : KaehlerMetric A) (hd : 0 < d) : SmoothRealFunction A where
  value x := Real.log ((h.traceMetric g).value x)
  smooth q := ((h.traceMetric g).smooth q).log (fun z _hz =>
    (h.traceMetric_pos g hd ((A.chart q).symm z)).ne')

lemma laplacian_logTrace (h g : KaehlerMetric A) (hd : 0 < d) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) :
    (h.laplacian (h.logTrace g hd)).localExpression q z =
      ((h.traceMetric g).localExpression q z)⁻¹ * (h.laplacian (h.traceMetric g)).localExpression q z -
      (((h.traceMetric g).localExpression q z)^2)⁻¹ *
        (h.energy (h.traceMetric g) (h.traceMetric g)).localExpression q z := by
  have hs := ((h.traceMetric g).smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  have hp : (h.traceMetric g).localExpression q z ≠ 0 :=
    (h.traceMetric_pos g hd ((A.chart q).symm z)).ne'
  have hx := (A.chart q).mapsTo_symm hz
  have hlocφ := h.laplacianValue_local (h.traceMetric g) q hx
  have hlocl := h.laplacianValue_local (h.logTrace g hd) q hx
  have hloce := h.energy_local (h.traceMetric g) (h.traceMetric g) q hz
  change (h.laplacianValue (h.logTrace g hd)) ((A.chart q).symm z) = _
  rw [hlocl,(A.chart q).right_inv hz]
  change _ = ((h.traceMetric g).localExpression q z)⁻¹ *
    h.laplacianValue (h.traceMetric g) ((A.chart q).symm z) - _
  rw [hlocφ,(A.chart q).right_inv hz]
  change _ = _ - _ * (h.energy (h.traceMetric g) (h.traceMetric g)).value ((A.chart q).symm z)
  change (h.energy (h.traceMetric g) (h.traceMetric g)).value ((A.chart q).symm z) = _ at hloce
  rw [hloce]
  simp only [linearizedMongeAmpere,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,gradientPair]
  have hm (b a : Fin d) : (h.logTrace g hd).hessian q z b a =
      (((h.traceMetric g).localExpression q z)⁻¹:ℝ)*(h.traceMetric g).hessian q z b a -
        ((((h.traceMetric g).localExpression q z)^2)⁻¹:ℝ)*
          star (holRealDeriv ((h.traceMetric g).localExpression q) z b)*
          holRealDeriv ((h.traceMetric g).localExpression q) z a :=
    potentialMatrix_log hs hp b a
  simp only [hm,mul_sub,Finset.sum_sub_distrib]
  have he (c : ℝ) (f : Fin d → Fin d → ℂ) :
      (∑ a, ∑ b, (h.matrix q z)⁻¹ a b*((c:ℂ)*f b a)).re =
        c*(∑ a, ∑ b, (h.matrix q z)⁻¹ a b*f b a).re := by
    have hh : (∑ a, ∑ b, (h.matrix q z)⁻¹ a b*((c:ℂ)*f b a)) =
        (c:ℂ)*(∑ a, ∑ b, (h.matrix q z)⁻¹ a b*f b a) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    rw [hh,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [Complex.sub_re]
  apply congrArg₂ (fun a b : ℝ => a-b)
  · exact he ((h.traceMetric g).localExpression q z)⁻¹ ((h.traceMetric g).hessian q z)
  · simpa only [mul_assoc] using he (((h.traceMetric g).localExpression q z)^2)⁻¹
      (fun b a => star (holRealDeriv ((h.traceMetric g).localExpression q) z b)*holRealDeriv ((h.traceMetric g).localExpression q) z a)

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI
