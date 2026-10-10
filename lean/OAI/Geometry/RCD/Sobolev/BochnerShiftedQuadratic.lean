import OAI.Geometry.RCD.Sobolev.BochnerQuadraticBound

namespace OAI

/-! # Shifted Hessian domination from the scalar dimensional Bochner bound

The same quadratic perturbation used for the unshifted Hessian works in
the positive form augmented by a scalar metric shift. Thus the scalar
finite-dimensional Bochner inequality suffices; a separate identification
of the local dimension is not needed for this step.
-/

noncomputable section
namespace RegularPointCoordinates

/-- Completing the square augments a finite-dimensional Bochner bound by
an arbitrary scalar shift. -/
theorem finite_bochner_shift_nonneg (N B delta b : ℝ) (hN : 0<N)
    (hBE : delta^2≤N*B) : 0≤B-2*b*delta+N*b^2 := by
  have hid : N*(B-2*b*delta+N*b^2) = (N*B-delta^2)+(delta-N*b)^2 := by ring
  have hprod : 0≤N*(B-2*b*delta+N*b^2) := by
    rw [hid]
    exact add_nonneg (sub_nonneg.mpr hBE) (sq_nonneg _)
  exact nonneg_of_mul_nonneg_right hprod hN

/-- Quadratic perturbation in the augmented positive form gives the exact
shifted directional Hessian bound. The source of the squared direction
is explicitly retained in `hdelta`. -/
theorem bochner_shifted_quadratic_perturbation_bound {m : ℕ}
    (B : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] ℝ)
    (delta : Euclidean m →ₗ[ℝ] ℝ) (N : ℝ)
    (hsym : ∀ a b, B a b=B b a)
    (hshift : ∀ a b, 0≤B a a-2*b*delta a+N*b^2)
    (f g q : Euclidean m) (c s H k b : ℝ)
    (hfg : B f q=2*c*B f g+2*H)
    (hgq : B g q=2*c*B g g+2*k)
    (hqq : B q q=4*c^2*B g g+8*c*k+4*s^2)
    (hdelta : delta q=2*c*delta g+2*s) :
    (H-b*s)^2≤(B f f-2*b*delta f+N*b^2)*s^2 := by
  let v := q-(2*c) • g
  have hfv : B f v=2*H := by
    dsimp only [v]
    rw [map_sub,map_smul]
    change B f q-(2*c)*B f g=2*H
    linarith only [hfg]
  have hvv : B v v=4*s^2 := by
    dsimp only [v]
    simp only [map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul]
    rw [hsym q g,hgq,hqq]
    ring
  have hdv : delta v=2*s := by
    dsimp only [v]
    rw [map_sub,map_smul,smul_eq_mul,hdelta]
    ring
  have hquad (t : ℝ) : 0≤(4*s^2)*(t*t)+(4*(H-b*s))*t+
      (B f f-2*b*delta f+N*b^2) := by
    have h := hshift (f+t • v) b
    simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul] at h
    rw [hsym v f,hfv,hvv,hdv] at h
    nlinarith only [h]
  have hd := discrim_le_zero hquad
  simp only [discrim] at hd
  nlinarith only [hd]

end RegularPointCoordinates

end

end OAI
