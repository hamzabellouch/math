import OAI.Analysis.CircleDomains.Topology.QuarterCircleAverage

namespace OAI

/-! Inversion sends each quarter circle to the opposite vertical quarter.
The principal flux density is the mean of its analytic inverse germ. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem star_quadrantNormal (s t : Bool) (θ : ℝ) :
    star (quadrantNormal s t θ) = quadrantNormal s (!t) θ := by
  cases t <;> apply Complex.ext <;> simp [quadrantNormal,quadrantSign]

 theorem inverse_quadrantPoint (r : ℝ) (s t : Bool) (θ : ℝ) :
    (quadrantPoint 0 r s t θ)⁻¹ = quadrantPoint 0 r⁻¹ s (!t) θ := by
  simp only [quadrantPoint,zero_add,mul_inv_rev,Complex.inv_eq_conj (quadrantNormal_norm s t θ),
    ← Complex.ofReal_inv]
  rw [show starRingEnd ℂ (quadrantNormal s t θ) = star (quadrantNormal s t θ) from rfl,
    star_quadrantNormal,mul_comm]

 theorem principal_quadrant_density {F H : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (he : ∀ z : ℂ, z ≠ 0 → H z⁻¹ = z⁻¹*F z) (θ : ℝ) :
    r*(∑ s : Bool, ∑ t : Bool,
      (F (quadrantPoint 0 r s t θ)*star (quadrantNormal s t θ)).re) =
      r^2*(∑ s : Bool, ∑ t : Bool, H (quadrantPoint 0 r⁻¹ s t θ)).re := by
  have hpoint (s t : Bool) :
      F (quadrantPoint 0 r s t θ)*star (quadrantNormal s t θ) =
        (r : ℂ)*H (quadrantPoint 0 r⁻¹ s (!t) θ) := by
    have hn : quadrantPoint 0 r s t θ ≠ 0 := by
      intro h
      have hh := quadrantPoint_dist 0 r s t θ
      rw [h,dist_self,abs_of_pos hr] at hh
      exact hr.ne' hh.symm
    rw [← inverse_quadrantPoint,he _ hn]
    simp only [quadrantPoint,zero_add,mul_inv_rev,
      Complex.inv_eq_conj (quadrantNormal_norm s t θ)]
    rw [← Complex.ofReal_inv]
    change F ((r : ℂ)*quadrantNormal s t θ)*star (quadrantNormal s t θ) =
      (r : ℂ)*(star (quadrantNormal s t θ)*(r⁻¹ : ℝ)*F ((r : ℂ)*quadrantNormal s t θ))
    rw [Complex.ofReal_inv]
    field_simp [show (r : ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr hr.ne']
  simp_rw [hpoint]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    ← Finset.mul_sum]
  simp only [Fintype.sum_bool,Bool.not_false,Bool.not_true,Complex.add_re]
  ring

end CircleDomainRigidity

end

end OAI
