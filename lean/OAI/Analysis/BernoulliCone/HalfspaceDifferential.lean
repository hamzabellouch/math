import OAI.Analysis.BernoulliCone.HomogeneousCalculus

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ENNReal ContDiff
namespace Bernoulli.Halfspace
open HarmonicKernel
variable {d : ℕ}

lemma squareQuotient_hasFDerivAt {u : Space d → ℝ} {e x : Space d}
    (hu : DifferentiableAt ℝ u x) (ht : 0 < inner ℝ x e) :
    HasFDerivAt (squareQuotient u e)
      ((inner ℝ x e)⁻¹ • ((2*u x) • fderiv ℝ u x)-
        (u x^2/(inner ℝ x e)^2) • innerSL ℝ e) x := by
  have hi : HasFDerivAt (fun y : Space d => inner ℝ y e) (innerSL ℝ e) x := by
    convert! (innerSL ℝ e).hasFDerivAt (x:=x) using 1
    funext y
    exact (real_inner_comm y e).symm
  have hh := (hu.hasFDerivAt.pow 2).mul ((hasDerivAt_inv ht.ne').comp_hasFDerivAt x hi)
  have he : (squareQuotient u e) =ᶠ[𝓝 x] (fun y=>u y^2/inner ℝ y e) := by
    filter_upwards [(continuous_id.inner continuous_const).continuousAt.preimage_mem_nhds
      (Ioi_mem_nhds ht)] with y hy
    change 0 < inner ℝ y e at hy
    simp only [squareQuotient,ite_eq_left hy]
  simp only [Function.comp_apply] at hh
  convert! hh.congr_of_eventuallyEq he using 1
  ext v
  simp only [sub_apply,smul_apply,smul_eq_mul,innerSL_apply_apply,add_apply,
    Nat.cast_ofNat,pow_one,Nat.reduceSub,nsmul_eq_mul]
  field_simp
  ring

lemma potential_gradient (x : Space d) :
    gradient (potential : Space d → ℝ) x = -rawKernel x • x := by
  apply ext_inner_right ℝ
  intro e
  rw [inner_gradient_left,real_inner_smul_left]
  have hh := radial_directional (contDiff_profile.differentiable (by simp)) x e
  rw [show (fun y : Space d=>profile (‖y‖^2))=potential from rfl] at hh
  rw [hh]
  simp only [rawKernel,kernelProfile]
  ring

lemma potential_nonneg (x : Space d) : 0 ≤ potential x := expNegInvGlue.nonneg _
lemma potential_pos {x : Space d} (hx : x∈ball (0:Space d) 1) : 0 < potential x := by
  apply expNegInvGlue.pos_of_pos
  rw [mem_ball_zero_iff] at hx
  nlinarith [norm_nonneg x]

lemma weightedQuotient_directional {u : Space d → ℝ} {e x : Space d}
    (hu : DifferentiableAt ℝ u x) (ht : 0 < inner ℝ x e) (he : ‖e‖=1) :
    inner ℝ (gradient (fun y=>potential y*squareQuotient u e y) x) e =
      -rawKernel x*u x^2 + potential x*(
        2*(u x/inner ℝ x e)*inner ℝ (gradient u x) e-(u x/inner ℝ x e)^2) := by
  have hφ := (contDiff_potential.differentiable (by simp) x).hasFDerivAt
  have hq := squareQuotient_hasFDerivAt hu ht
  have hp := hφ.mul hq
  change HasFDerivAt (fun y=>potential y*squareQuotient u e y) _ x at hp
  rw [inner_gradient_left,hp.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,sub_apply,innerSL_apply_apply]
  simp only [← inner_gradient_left,potential_gradient,real_inner_smul_left,
    real_inner_self_eq_norm_sq,he]
  simp only [squareQuotient,ite_eq_left ht,one_pow,mul_one]
  field_simp
  ring

lemma radial_outer_identity {u : Space d → ℝ} {L : ℝ≥0}
    (hm : GlobalMinimizer u) (hL : LipschitzWith L u)
    (hom : ∀r:ℝ, 0<r → ∀x, u (r•x)=r*u x) :
    (∫ x in ball (0:Space d) 2, potential x*‖gradient u x‖^2-rawKernel x*u x^2)=0 := by
  have hφ : Test (ball (0:Space d) 2) potential := by
    have he : (potential : Space d → ℝ)=scaledPotential 1 0 := by
      funext x; simp [potential,scaledPotential]
    rw [he]
    exact scaledPotential_test (by norm_num) 0 (closedBall_subset_ball (by norm_num))
  have hh := hm.outerVariation hL (by norm_num : 0 < (2:ℝ)) hφ
  rw [← hh]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hL.ae_differentiableAt] with x hx
  have he := ConeCalculus.euler_identity hx hom
  rw [← inner_gradient_left] at he
  simp only [inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq,potential_gradient]
  rw [he]
  ring
end Bernoulli.Halfspace

end
end

end OAI
