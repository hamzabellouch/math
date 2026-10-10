import OAI.Analysis.CircleDomains.Topology.CircleMobiusImage

namespace OAI

/-!
# Holomorphy of the explicit normalizing Möbius maps

The affine chart at infinity is the rational function z / (a + b z).
This gives a nonzero derivative there as well as in every finite chart.
-/

open Set Filter Function
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity

@[simp] theorem finiteCoord_coe (z : ℂ) : finiteCoord (z : Sphere) = z := rfl

theorem finiteCoord_sphereInv_coe (z : ℂ) : finiteCoord (sphereInv (z : Sphere)) = z⁻¹ := by
  change CannonMobius.coordinate (CannonMobius.inv (z : Sphere)) = z⁻¹
  exact CannonMobius.coordinate_inv_coe z

@[simp] theorem chart_coe_apply (p : ℂ) (q : Sphere) :
    chart (p : Sphere) q = finiteCoord q := by
  simp [chart]

@[simp] theorem chart_coe_self (p : ℂ) : chart (p : Sphere) (p : Sphere) = p := by
  simp [finiteCoord]

@[simp] theorem chart_infty_apply (q : Sphere) :
    chart OnePoint.infty q = finiteCoord (sphereInv q) := by simp [chart]

@[simp] theorem sphereInv_infty : sphereInv OnePoint.infty = ((0 : ℂ) : Sphere) := rfl

@[simp] theorem sphereInv_zero : sphereInv ((0 : ℂ) : Sphere) = OnePoint.infty := by
  simp [sphereInv]

@[simp] theorem chart_infty_self : chart OnePoint.infty OnePoint.infty = 0 := by
  simp [finiteCoord]

@[simp] theorem chartSymm_coe_apply (p z : ℂ) : chartSymm (p : Sphere) z = (z : Sphere) := by
  simp [chartSymm]

@[simp] theorem affineSphere_coe (a b : ℂ) (ha : a ≠ 0) (z : ℂ) :
    affineSphere a b ha (z : Sphere) = ((a * z + b : ℂ) : Sphere) := rfl

@[simp] theorem affineSphere_infty (a b : ℂ) (ha : a ≠ 0) :
    affineSphere a b ha OnePoint.infty = OnePoint.infty := rfl

theorem isConformalAt_inversion (p : Sphere) : IsConformalAt CannonMobius.inversion p := by
  refine ⟨CannonMobius.inversion.continuous.continuousAt, ?_⟩
  cases p using OnePoint.rec with
  | infty =>
    refine ⟨1, one_ne_zero, ?_⟩
    have heq : (fun z => chart (sphereInv OnePoint.infty)
        (sphereInv (chartSymm OnePoint.infty z))) = id := by
      funext z
      simp only [sphereInv_infty, chart_coe_apply, chartSymm, ite_true,
        sphereInv_sphereInv, finiteCoord, OnePoint.elim_some, id_eq]
    change HasDerivAt (fun z => chart (sphereInv OnePoint.infty)
      (sphereInv (chartSymm OnePoint.infty z))) 1 (chart OnePoint.infty OnePoint.infty)
    rw [heq, chart_infty_self]
    exact hasDerivAt_id 0
  | coe z =>
    by_cases hz : z = 0
    · subst z
      refine ⟨1, one_ne_zero, ?_⟩
      have heq : (fun w => chart (sphereInv ((0 : ℂ) : Sphere))
          (sphereInv (chartSymm ((0 : ℂ) : Sphere) w))) = id := by
        funext w
        simp only [sphereInv_zero, chart_infty_apply, chartSymm_coe_apply,
          sphereInv_sphereInv, finiteCoord, OnePoint.elim_some, id_eq]
      change HasDerivAt (fun w => chart (sphereInv ((0 : ℂ) : Sphere))
        (sphereInv (chartSymm ((0 : ℂ) : Sphere) w))) 1 (chart ((0 : ℂ) : Sphere) ((0 : ℂ) : Sphere))
      rw [heq, chart_coe_self]
      exact hasDerivAt_id 0
    · refine ⟨-(z ^ 2)⁻¹, neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ hz)), ?_⟩
      have hfp : sphereInv (z : Sphere) = ((z⁻¹ : ℂ) : Sphere) := by simp [sphereInv, hz]
      change HasDerivAt (fun w => chart (sphereInv (z : Sphere))
        (sphereInv (chartSymm (z : Sphere) w))) _ (chart (z : Sphere) (z : Sphere))
      simpa only [hfp, chart_coe_apply, chartSymm_coe_apply,
        finiteCoord_sphereInv_coe, finiteCoord_coe] using hasDerivAt_inv hz

theorem affine_chart_at_infinity (a b : ℂ) (ha : a ≠ 0) (z : ℂ) :
    chart OnePoint.infty (affineSphere a b ha (chartSymm OnePoint.infty z)) = z / (a + b * z) := by
  by_cases hz : z = 0
  · simp [hz, chart, chartSymm, sphereInv, affineSphere, finiteCoord]
  · have hden : a * z⁻¹ + b = (a + b * z) / z := by field_simp
    have hs : chartSymm OnePoint.infty z = ((z⁻¹ : ℂ) : Sphere) := by
      simp [chartSymm, sphereInv, hz]
    rw [hs, affineSphere_coe]
    rw [chart_infty_apply, finiteCoord_sphereInv_coe, hden, inv_div]

theorem isConformalAt_affineSphere (a b : ℂ) (ha : a ≠ 0) (p : Sphere) :
    IsConformalAt (affineSphere a b ha) p := by
  refine ⟨(affineSphere a b ha).continuous.continuousAt, ?_⟩
  cases p using OnePoint.rec with
  | infty =>
    refine ⟨a⁻¹, inv_ne_zero ha, ?_⟩
    have hd := (hasDerivAt_id (0 : ℂ)).div
      ((hasDerivAt_const (0 : ℂ) a).add ((hasDerivAt_id (0 : ℂ)).const_mul b))
      (by simpa using ha)
    have heq : (fun z => chart (affineSphere a b ha OnePoint.infty)
        (affineSphere a b ha (chartSymm OnePoint.infty z))) = fun z => z / (a + b * z) := by
      funext z
      exact affine_chart_at_infinity a b ha z
    rw [heq, chart_infty_self]
    have hscalar : (1 * (a + b * 0) - 0 * (0 + b * 1)) / (a + b * 0) ^ 2 = a⁻¹ := by
      simp only [mul_zero, add_zero, zero_mul, sub_zero, one_mul]
      field_simp
    convert hd using 1
    · rfl
    · exact hscalar.symm
  | coe z =>
    refine ⟨a, ha, ?_⟩
    simpa only [affineSphere_coe, chart_coe_apply, chartSymm_coe_apply,
      finiteCoord, OnePoint.elim_some, id_eq, mul_one] using
        ((hasDerivAt_id z).const_mul a).add_const b

end CircleDomainRigidity

end

end OAI
