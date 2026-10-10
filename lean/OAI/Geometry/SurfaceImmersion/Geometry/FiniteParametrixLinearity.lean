import OAI.Geometry.SurfaceImmersion.Geometry.FiniteParametrix

namespace OAI

/-! Linearity of the finite homogeneous correction in its initial amplitude. -/
noncomputable section
namespace ClosedSurfaceR4.FiniteParametrix

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

def homogeneousLM (A : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) : ℕ → E →ₗ[ℝ] E
  | 0 => LinearMap.id
  | j + 1 => (LinearMap.id - S.comp A).comp (homogeneousLM A S j)

lemma homogeneousLM_apply (A : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) (j : ℕ) (z : E) :
    homogeneousLM A S j z = improve A S 0 z j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [homogeneousLM, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply, ih, improve, sub_zero]

end ClosedSurfaceR4.FiniteParametrix

end

end OAI
