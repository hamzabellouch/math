import OAI.Analysis.AncientFlat.Weighted.WeightedScaling

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace FlatWeighted
open ParabolicAnnular
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
omit [FiniteDimensional ℝ V] in
lemma profile_argument_scale (r : ℝ) (hr : 0<r) (p : V × ℝ) :
    ‖(scale r p).1‖^2/Real.sqrt (-(scale r p).2)=‖p.1‖^2/Real.sqrt (-p.2) := by
  have h4 : r^4=(r^2)^2 := by ring
  simp only [scale,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  rw [show -(r^4*p.2)=r^4*(-p.2) by ring,Real.sqrt_mul (pow_nonneg hr.le 4),h4,Real.sqrt_sq (sq_nonneg r),mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hr.ne')
omit [FiniteDimensional ℝ V] in
lemma profilePrincipal_scale (G : ℝ → ℝ) (r : ℝ) (hr : 0<r) (p : V × ℝ) :
    profilePrincipal G (scale r p)=profilePrincipal G p := by
  simp only [profilePrincipal,profile_argument_scale r hr]
omit [FiniteDimensional ℝ V] in
lemma profilePotential_scale (G : ℝ → ℝ) (r : ℝ) (hr : 0<r) (p : V × ℝ) :
    r^4*profilePotential G (scale r p)=profilePotential G p := by
  unfold profilePotential
  rw [profile_argument_scale r hr]
  dsimp only [scale]
  rw [show -(r^4*p.2)=r^4*(-p.2) by ring,mul_inv_rev]
  have hr0 : r^4≠0 := pow_ne_zero 4 hr.ne'
  field_simp
end FlatWeighted

end

end OAI
