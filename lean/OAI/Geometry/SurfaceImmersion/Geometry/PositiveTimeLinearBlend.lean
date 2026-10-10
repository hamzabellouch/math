import OAI.Geometry.SurfaceImmersion.Atlas.TimeCoordinateTransition

namespace OAI

/-! Positive transverse coordinate changes can be blended while keeping
the common time differential and an invertible derivative. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma time_linear_bijective (L : Base →L[ℝ] Base)
    (hsecond : ∀ v, L v 1 = v 1) (hfirst : L ![1,0] 0 ≠ 0) : Function.Bijective L := by
  have hi : Function.Injective L := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm
    · intro v hv
      have hv1 : v 1 = 0 := (hsecond v).symm.trans (congrFun hv 1)
      have he : v = (v 0) • (![1,0] : Base) := by
        ext i
        fin_cases i <;> simp [hv1]
      have hv0 : v 0 = 0 := by
        have hh := congrFun hv 0
        rw [he,map_smul] at hh
        change v 0 * L ![1,0] 0 = 0 at hh
        exact (mul_eq_zero.mp hh).resolve_right hfirst
      show v = 0
      ext i
      fin_cases i
      · exact hv0
      · exact hv1
    · exact bot_le
  exact ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := L.toLinearMap) rfl).mp hi⟩

theorem positive_time_linear_blend (L : Base →L[ℝ] Base)
    (hsecond : ∀ v, L v 1 = v 1) (hfirst : 0 < L ![1,0] 0)
    {θ : ℝ} (hθ : θ ∈ Icc (0:ℝ) 1) :
    Function.Bijective ((1-θ) • ContinuousLinearMap.id ℝ Base + θ • L) := by
  let D := (1-θ) • ContinuousLinearMap.id ℝ Base + θ • L
  apply time_linear_bijective D
  · intro v
    change (1-θ)*v 1+θ*(L v 1) = v 1
    rw [hsecond]
    ring
  · have ha : 0 < 1-θ+θ*(L ![1,0] 0) := by
      by_cases hzero : θ = 0
      · rw [hzero]; norm_num
      · have hpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hzero)
        have hprod := mul_pos hpos hfirst
        linarith [hθ.2]
    have he : D ![1,0] 0 = 1-θ+θ*(L ![1,0] 0) := by
      change (1-θ)*1+θ*(L ![1,0] 0) = _
      ring
    rw [he]
    exact ne_of_gt ha

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
