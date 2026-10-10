import OAI.Analysis.CircleDomains.Selection.PrincipalQuadrantGeometry

namespace OAI

/-! The analytic inverse mean equals one, so the principal outer flux is
exactly the area factor. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem principal_quadrantFlux_of_inverse_mean {F H : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hH : ContinuousOn H (closedBall 0 r⁻¹))
    (hmean : Real.circleAverage H 0 r⁻¹ = 1)
    (he : ∀ z : ℂ, z ≠ 0 → H z⁻¹ = z⁻¹*F z) :
    quadrantFlux F 0 r = 2*Real.pi*r^2 := by
  have hQ (s t : Bool) : Continuous (fun θ => H (quadrantPoint 0 r⁻¹ s t θ)) := by
    apply hH.comp_continuous
    · change Continuous (fun θ => (0 : ℂ)+(r⁻¹ : ℝ)*Complex.equivRealProdCLM.symm
        (quadrantSign s*Real.cos θ,quadrantSign t*Real.sin θ))
      fun_prop
    · intro θ
      rw [mem_closedBall,quadrantPoint_dist,abs_of_pos (inv_pos.mpr hr)]
  have hi : IntervalIntegrable (fun θ => ∑ s : Bool, ∑ t : Bool,
      H (quadrantPoint 0 r⁻¹ s t θ)) volume 0 (Real.pi/2) :=
    (continuous_finsetSum _ (fun s _ => continuous_finsetSum _ (fun t _ => hQ s t))).intervalIntegrable _ _
  have hRe := Complex.reCLM.intervalIntegral_comp_comm hi
  have hmeanR := congrArg Complex.re hmean
  simp only [Real.circleAverage_def,Complex.smul_re,smul_eq_mul,Complex.one_re] at hmeanR
  have hπ : (2 : ℝ)*Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hval : (∫ θ in (0 : ℝ)..(2*Real.pi), H (circleMap 0 r⁻¹ θ)).re = 2*Real.pi := by
    apply mul_left_cancel₀ (inv_ne_zero hπ)
    simpa only [inv_mul_cancel₀ hπ] using hmeanR
  calc
    quadrantFlux F 0 r = r^2*(∫ θ in (0 : ℝ)..(Real.pi/2),
        (∑ s : Bool, ∑ t : Bool, H (quadrantPoint 0 r⁻¹ s t θ)).re) := by
      unfold quadrantFlux
      simp_rw [principal_quadrant_density hr he]
      rw [intervalIntegral.integral_const_mul]
    _ = r^2*(∫ θ in (0 : ℝ)..(Real.pi/2),
        ∑ s : Bool, ∑ t : Bool, H (quadrantPoint 0 r⁻¹ s t θ)).re := by
      exact congrArg (fun x : ℝ => r^2*x) hRe
    _ = r^2*(∫ θ in (0 : ℝ)..(2*Real.pi), H (circleMap 0 r⁻¹ θ)).re := by
      rw [integral_four_quadrants (inv_nonneg.mpr hr.le) hH]
    _ = 2*Real.pi*r^2 := by rw [hval]; ring

end CircleDomainRigidity

end

end OAI
