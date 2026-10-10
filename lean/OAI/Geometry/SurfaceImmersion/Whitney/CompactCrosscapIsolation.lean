import OAI.Geometry.SurfaceImmersion.Geometry.CompactFixedJet
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapKernelCapture

namespace OAI

/-! A compact smooth family with one fixed nondegenerate direction jet
has a common neighborhood containing no other singularities. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem compact_crosscap_isolation {K : Set ℝ} (hK : IsCompact K)
    (F : ℝ → Base → ProjectionTarget 3)
    (hF : ∀ t ∈ K, ContDiff ℝ ∞ (F t))
    (hD : Continuous (fun z : ℝ × Base => fderiv ℝ (F z.1) z.2))
    (hJ : Continuous (fun z : ℝ × (Base × ℝ) =>
      fderiv ℝ (surfaceDirection (F z.1) true) z.2))
    (p : Base) (D : Base →L[ℝ] ProjectionTarget 3)
    (J : (Base × ℝ) →L[ℝ] ProjectionTarget 3)
    (hfixD : ∀ t ∈ K, fderiv ℝ (F t) p = D)
    (hfixJ : ∀ t ∈ K, fderiv ℝ (surfaceDirection (F t) true) (p,0) = J)
    (hzero : D (![0,1] : Base) = 0)
    (htrans : D (![1,0] : Base) ≠ 0) (hreg : Function.Bijective J) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ K, ∀ x ∈ ball p r,
      (¬ Function.Injective (fderiv ℝ (F t) x) ↔ x = p) := by
  let L := ContinuousLinearEquiv.ofBijective J
    (LinearMap.ker_eq_bot.mpr hreg.1) (LinearMap.range_eq_top.mpr hreg.2)
  obtain ⟨r₀,hr₀,hinj⟩ := compact_fixed_jet_injectivity hK
    (fun t => surfaceDirection (F t) true) (fun t ht => surfaceDirection_smooth (hF t ht) true)
    hJ (p,0) L hfixJ
  obtain ⟨ε,hε,hcapture⟩ := kernel_capture_near D true 0
    (by simpa [tangentRay] using hzero) (by simpa [tangentRayVelocity] using htrans)
    (half_pos hr₀)
  obtain ⟨U,hU,hpU,hnear⟩ := compact_fixed_value_neighborhood hK hD p D hfixD hε
  obtain ⟨s,hs,hsU⟩ := Metric.isOpen_iff.mp hU p hpU
  let r := min s (r₀/2)
  have hr : 0 < r := lt_min hs (half_pos hr₀)
  refine ⟨r,hr,?_⟩
  intro t ht x hx
  have hzt : surfaceDirection (F t) true (p,0) = 0 := by
    simpa only [surfaceDirection,hfixD t ht,tangentRay,ite_true,zero_smul,zero_add] using hzero
  constructor
  · intro hbad
    have hclose : ‖fderiv ℝ (F t) x-D‖ < ε := by
      simpa only [dist_eq_norm] using hnear t ht x
        (hsU (ball_subset_ball (min_le_left _ _) hx))
    obtain ⟨v,hv,hker⟩ := hcapture _ hclose hbad
    have hball : (x,v) ∈ ball (p,(0:ℝ)) r₀ := by
      rw [mem_ball,dist_eq_norm,Prod.norm_def]
      apply max_lt
      · exact (mem_ball.mp hx).trans_le (min_le_right _ _) |>.trans (half_lt_self hr₀)
      · simpa only [Prod.snd_sub,sub_zero,Real.norm_eq_abs] using hv.trans (half_lt_self hr₀)
    exact congrArg Prod.fst (hinj t ht hball (mem_ball_self hr₀) (hker.trans hzt.symm))
  · intro heq hi
    subst x
    have hz : fderiv ℝ (F t) p (![0,1] : Base) = fderiv ℝ (F t) p 0 := by
      rw [hfixD t ht,map_zero]
      exact hzero
    have hh := congrFun (hi hz) 1
    norm_num at hh

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
