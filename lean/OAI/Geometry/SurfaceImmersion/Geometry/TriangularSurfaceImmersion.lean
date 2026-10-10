import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapPairModel

namespace OAI

/-! Immersion criterion for the local surface (x, xy, h(x,y)). This isolates
the single derivative that must stay positive in a supported cancellation. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma planeLinear_apply (L : Base →L[ℝ] ℝ) (v : Base) :
    L v = v 0 * L ![1,0] + v 1 * L ![0,1] := by
  have he : v = v 0 • (![1,0] : Base) + v 1 • (![0,1] : Base) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [he]
  simp only [map_add,map_smul,smul_eq_mul]

def triangularSurfaceCoordinates (h : Base → ℝ) (x : Base) : Fin 3 → ℝ :=
  ![x 0,x 0*x 1,h x]

def triangularSurfaceDerivative (x : Base) (D : Base →L[ℝ] ℝ) :
    Base →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,
    x 0 • ContinuousLinearMap.proj 1 + x 1 • ContinuousLinearMap.proj 0,D]

lemma triangularSurfaceCoordinates_hasFDerivAt {h : Base → ℝ} {x : Base}
    (hh : DifferentiableAt ℝ h x) :
    HasFDerivAt (triangularSurfaceCoordinates h)
      (triangularSurfaceDerivative x (fderiv ℝ h x)) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) x
  · exact (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) x).mul
      (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) x)
  · exact hh.hasFDerivAt

lemma triangularSurfaceDerivative_injective {x : Base} {D : Base →L[ℝ] ℝ}
    (h : x 0 ≠ 0 ∨ D ![0,1] ≠ 0) :
    Function.Injective (triangularSurfaceDerivative x D) := by
  intro v w he
  have h0 : v 0 = w 0 := congrFun he 0
  have h1 : x 0*v 1 + x 1*v 0 = x 0*w 1 + x 1*w 0 := congrFun he 1
  have h2 : D v = D w := congrFun he 2
  have hvw : v 1 = w 1 := by
    rcases h with hx | hd
    · rw [h0] at h1
      exact mul_left_cancel₀ hx (add_right_cancel h1)
    · rw [planeLinear_apply D v,planeLinear_apply D w,h0] at h2
      have hh : (v 1-w 1)*D ![0,1] = 0 := by nlinarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hd)
  ext i
  fin_cases i
  · exact h0
  · exact hvw

def triangularSurface (h : Base → ℝ) : Base → ProjectionTarget 3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ∘ triangularSurfaceCoordinates h

lemma triangularSurface_smooth {h : Base → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (triangularSurface h) := by
  apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact (ContinuousLinearMap.proj (0 : Fin 2) : Base →L[ℝ] ℝ).contDiff
  · exact ((ContinuousLinearMap.proj (0 : Fin 2) : Base →L[ℝ] ℝ).contDiff).mul ((ContinuousLinearMap.proj (1 : Fin 2) : Base →L[ℝ] ℝ).contDiff)
  · exact hh

theorem triangularSurface_immersion {h : Base → ℝ} (hh : ContDiff ℝ ∞ h)
    (hpositive : ∀ x : Base, x 0 = 0 → 0 < fderiv ℝ h x ![0,1]) (x : Base) :
    Function.Injective (fderiv ℝ (triangularSurface h) x) := by
  have hd := triangularSurfaceCoordinates_hasFDerivAt (hh.differentiable (by simp) x)
  have hi : Function.Injective (triangularSurfaceDerivative x (fderiv ℝ h x)) := by
    apply triangularSurfaceDerivative_injective
    by_cases hx : x 0 = 0
    · exact Or.inr (ne_of_gt (hpositive x hx))
    · exact Or.inl hx
  rw [triangularSurface,fderiv_comp x
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.differentiableAt hd.differentiableAt,
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.fderiv,hd.fderiv]
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.injective.comp hi

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
