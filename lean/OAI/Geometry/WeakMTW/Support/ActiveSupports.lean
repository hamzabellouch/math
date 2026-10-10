import Mathlib
import OAI.Geometry.WeakMTW.Variations.ActionHessian
import OAI.Geometry.WeakMTW.Variations.CostSplitting
import OAI.Geometry.WeakMTW.Support.FiniteActiveGraph

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry RadialHessianCalculus
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]
  {ι : Type*} [Fintype ι] [Nonempty ι]

 def activeSupport (y : ι → M) (h : ι → ℝ) (p : M)
    (a : TangentSpace (model n) p) (ℓ : ℝ) (z : M) : ℝ :=
    finitePotential y h p + (cost p (exp p (ℓ•a))-cost z (exp p (ℓ•a))) / ℓ

 theorem activeSupport_le (y : ι → M) (h : ι → ℝ) (p : M)
    {a : TangentSpace (model n) p} (ha : a ∈ activeVelocities y h p)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ₁ : ℓ < 1) (z : M) :
    activeSupport y h p a ℓ z ≤ finitePotential y h z := by
  obtain ⟨ham,i,hai,hia⟩ := ha
  have hsplit := cost_triangle_split z (exp p (ℓ•a)) (y i) hℓ (sub_pos.mpr hℓ₁)
  have hd := minimizing_shortened_dist ham hℓ.le hℓ₁.le (le_refl 1)
  simp only [one_smul,hai] at hd
  have hcost : cost (exp p (ℓ•a)) (y i) = (1-ℓ)^2*‖a‖^2/2 := by
    unfold cost
    rw [hd,mul_pow]
  have hcostp : cost p (y i) = ‖a‖^2/2 := by
    unfold cost
    rw [← hai,show dist p (exp p a) = ‖a‖ from ham]
  have hsplit' : cost z (y i) ≤ cost z (exp p (ℓ•a)) / ℓ + (1-ℓ)*‖a‖^2/2 := by
    rw [add_sub_cancel,div_one,hcost] at hsplit
    convert hsplit using 1
    field_simp [hℓ₁.ne]
  have hge := finitePotential_ge y h z i
  unfold activeSupport
  rw [hia,hcostp,minimizing_shortened_cost ham hℓ.le hℓ₁.le]
  have hid : ‖a‖^2/2-(ℓ^2*‖a‖^2/2)/ℓ = (1-ℓ)*‖a‖^2/2 := by
    field_simp [hℓ.ne']
  rw [sub_div]
  linarith

omit [IsManifold (model n) ∞ M]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem activeSupport_contact (y : ι → M) (h : ι → ℝ) (p : M)
    (a : TangentSpace (model n) p) (ℓ : ℝ) :
    activeSupport y h p a ℓ p = finitePotential y h p := by
  simp only [activeSupport,sub_self,zero_div,add_zero]

 theorem activeSupport_chart_smooth (y : ι → M) (h : ι → ℝ) (p : M)
    {a : TangentSpace (model n) p} (ha : a ∈ activeVelocities y h p)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ₁ : ℓ < 1) :
    ContDiffAt ℝ ∞ (fun z => activeSupport y h p a ℓ ((chartAt (Model n) p).symm z))
      (chartAt (Model n) p p) := by
  exact contDiffAt_const.add ((contDiffAt_const.sub
    (initialCost_geometry p (strict_radial_mem_injectivity ha.1 hℓ.le hℓ₁)).1).div_const ℓ)

 theorem activeSupport_chart_derivative (y : ι → M) (h : ι → ℝ) (p : M)
    {a : TangentSpace (model n) p} (ha : a ∈ activeVelocities y h p)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ₁ : ℓ < 1) (ξ : TangentSpace (model n) p) :
    fderiv ℝ (fun z => activeSupport y h p a ℓ ((chartAt (Model n) p).symm z))
      (chartAt (Model n) p p) (tangentChartLinear p ξ) = inner ℝ a ξ := by
  have hi := strict_radial_mem_injectivity ha.1 hℓ.le hℓ₁
  have hf := (initialCost_geometry p hi).1.differentiableAt (by simp)
  have hd := ((hf.hasFDerivAt.neg.const_add (cost p (exp p (ℓ•a)))).mul_const ℓ⁻¹).const_add (finitePotential y h p)
  have hd' : fderiv ℝ (fun z => activeSupport y h p a ℓ ((chartAt (Model n) p).symm z))
      (chartAt (Model n) p p) = ℓ⁻¹ • (-fderiv ℝ (initialCost p (exp p (ℓ•a))) (chartAt (Model n) p p)) := by
    exact (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z => by
      simp only [activeSupport,Pi.neg_apply,initialCost,sub_eq_add_neg,div_eq_mul_inv]))).fderiv
  rw [hd']
  simp only [smul_apply,neg_apply,smul_eq_mul]
  rw [(initialCost_geometry p hi).2.1]
  simp only [map_smul,smul_apply,smul_eq_mul,neg_neg]
  have hpmetric := stateChart_pairing p p (mem_chart_source (Model n) p) a ξ
  rw [← tangentChartLinear_eq,← tangentChartLinear_eq] at hpmetric
  rw [hpmetric]
  field_simp [hℓ.ne']

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
