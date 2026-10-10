import OAI.Geometry.SurfaceImmersion.Whitney.RoundedReturnArc
import OAI.Geometry.SurfaceImmersion.Whitney.GraphJoinArc

namespace OAI

/-! The explicit roundings stay between their two graph branches. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing

lemma convex_height_bounds {t u v l h : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hu : u ∈ Icc l h) (hv : v ∈ Icc l h) :
    (1-t)*u+t*v ∈ Icc l h := by
  have ht' : 0 ≤ 1-t := sub_nonneg.mpr ht.2
  constructor
  · calc
      l = (1-t)*l+t*l := by ring
      _ ≤ (1-t)*u+t*v := add_le_add (mul_le_mul_of_nonneg_left hu.1 ht')
        (mul_le_mul_of_nonneg_left hv.1 ht.1)
  · calc
      (1-t)*u+t*v ≤ (1-t)*h+t*h := add_le_add (mul_le_mul_of_nonneg_left hu.2 ht')
        (mul_le_mul_of_nonneg_left hv.2 ht.1)
      _ = h := by ring

lemma roundedReturnCurve_height_bounds {f g : ℝ → ℝ} {a b t l h : ℝ}
    (hf : f (a+b*t^2) ∈ Icc l h) (hg : g (a+b*t^2) ∈ Icc l h) :
    (roundedReturnCurve f g a b t) 1 ∈ Icc l h :=
  convex_height_bounds (centeredSmoothStep_bounds t) hf hg

lemma graphJoinCurve_height_bounds {f g : ℝ → ℝ} {t l h : ℝ}
    (hf : f t ∈ Icc l h) (hg : g t ∈ Icc l h) :
    (graphJoinCurve f g t) 1 ∈ Icc l h :=
  convex_height_bounds (centeredSmoothStep_bounds t) hf hg

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
