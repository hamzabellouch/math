import OAI.Geometry.SurfaceImmersion.Geometry.PlaneDerivativeInjectivity

namespace OAI

/-! Uniform isolation for a compact family of nondegenerate planar zeros.
The differential may vary with the homotopy parameter. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem compact_plane_jet_injectivity {K : Set ℝ} (hK : IsCompact K)
    (F : ℝ → Base → Base) (hF : ∀ t ∈ K, ContDiff ℝ ∞ (F t))
    (hD : Continuous (fun z : ℝ × Base => fderiv ℝ (F z.1) z.2)) (p : Base)
    (hI : ∀ t ∈ K, Function.Bijective (fderiv ℝ (F t) p)) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ K, (ball p r).InjOn (F t) := by
  have hJ : ContinuousOn (fun t => (fderiv ℝ (F t) p).inverse) K := by
    intro t ht
    let L := ContinuousLinearEquiv.ofBijective (fderiv ℝ (F t) p)
      (LinearMap.ker_eq_bot.mpr (hI t ht).1) (LinearMap.range_eq_top.mpr (hI t ht).2)
    have hi : (fderiv ℝ (F t) p).IsInvertible := ⟨L,rfl⟩
    have hinv : ContDiffAt ℝ 0 ContinuousLinearMap.inverse (fderiv ℝ (F t) p) :=
      hi.contDiffAt_map_inverse
    have hP : Continuous (fun s : ℝ => fderiv ℝ (F s) p) :=
      hD.comp (continuous_id.prodMk continuous_const)
    have hJt : ContinuousAt (fun s : ℝ => (fderiv ℝ (F s) p).inverse) t :=
      ContinuousAt.comp (g := ContinuousLinearMap.inverse)
        (f := fun s : ℝ => fderiv ℝ (F s) p) hinv.continuousAt hP.continuousAt
    exact hJt.continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hJ
  let c : ℝ := (2*(|C|+1))⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  have hdiff : Continuous (fun z : ℝ × Base =>
      fderiv ℝ (F z.1) z.2-fderiv ℝ (F z.1) p) :=
    hD.sub (hD.comp (continuous_fst.prodMk continuous_const))
  obtain ⟨U,hU,hpU,hnear⟩ := compact_fixed_value_neighborhood hK hdiff p
    (0 : Base →L[ℝ] Base) (fun _ _ => sub_self _) hc
  obtain ⟨r,hr,hrU⟩ := Metric.isOpen_iff.mp hU p hpU
  refine ⟨r,hr,?_⟩
  intro t ht
  let L := ContinuousLinearEquiv.ofBijective (fderiv ℝ (F t) p)
    (LinearMap.ker_eq_bot.mpr (hI t ht).1) (LinearMap.range_eq_top.mpr (hI t ht).2)
  have hLI : (fderiv ℝ (F t) p).inverse = L.symm.toContinuousLinearMap := by
    change (L.toContinuousLinearMap).inverse = _
    exact ContinuousLinearMap.inverse_equiv L
  have hLn : ‖L.symm.toContinuousLinearMap‖ ≤ |C| := by
    rw [←hLI]
    exact (hC t ht).trans (le_abs_self C)
  apply near_plane_equiv_derivative_injOn L
    (fun x _ => (hF t ht).differentiable (by simp) x) (convex_ball p r) (c := c)
  · calc
      _ ≤ |C| * c := mul_le_mul_of_nonneg_right hLn hc.le
      _ < 1 := by
        dsimp [c]
        rw [←div_eq_mul_inv]
        apply (div_lt_iff₀ (by positivity)).mpr
        linarith [abs_nonneg C]
  · intro x hx
    have hh : ‖fderiv ℝ (F t) x-fderiv ℝ (F t) p‖ < c := by
      simpa only [dist_zero_right] using hnear t ht x (hrU hx)
    exact hh.le

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
