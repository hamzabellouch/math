import OAI.Analysis.BernoulliCone.CompactGradient

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ENNReal ContDiff
namespace Bernoulli.Halfspace
open HarmonicKernel
variable {d : ℕ}

lemma radial_potential_test : Test (ball (0:Space d) 2) potential := by
  have he : (potential : Space d → ℝ)=scaledPotential 1 0 := by
    funext x; simp [potential,scaledPotential]
  rw [he]
  exact scaledPotential_test (by norm_num) 0 (closedBall_subset_ball (by norm_num))

lemma radial_outer_integrable {u : Space d → ℝ} {L : ℝ≥0} (hL : LipschitzWith L u) :
    IntegrableOn (fun x=> potential x*‖gradient u x‖^2-rawKernel x*u x^2) (ball (0:Space d) 2) := by
  have hu := LipschitzSobolev.h1_ball hL 0 2
  have hi := (memLp_two_iff_integrable_sq_norm hu.2.1.aestronglyMeasurable).mp hu.2.1
  obtain ⟨C,hC⟩ := (radial_potential_test (d:=d)).2.1.exists_bound_of_continuous contDiff_potential.continuous
  have hi' := hi.bdd_mul contDiff_potential.continuous.aestronglyMeasurable (Eventually.of_forall hC)
  have hq : Integrable (fun x=>rawKernel x*u x^2) volume :=
    (contDiff_rawKernel.continuous.mul (hL.continuous.pow 2)).integrable_of_hasCompactSupport rawKernel_compact.mul_right
  exact hi'.sub hq.integrableOn

/-- Ground-state equality for a true homogeneous minimizing cone supported in
one closed halfspace. This uses a Lipschitz perspective competitor, not a
regularity assumption or a boundary trace quotient. -/
theorem gradient_parallel_of_halfspace_support {u : Space d → ℝ} {L : ℝ≥0}
    (hm : GlobalMinimizer u) (hL : LipschitzWith L u)
    (hom : ∀r:ℝ, 0<r → ∀x, u (r•x)=r*u x)
    {e : Space d} (he : ‖e‖=1) (hz : ∀x, inner ℝ x e ≤ 0 → u x=0) :
    ∀ᵐ x ∂volume.restrict (ball (0:Space d) 1),
      gradient u x=(u x/inner ℝ x e) • e := by
  let B := ball (0:Space d) 2
  let μ := volume.restrict B
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let q := fun x=>potential x*squareQuotient u e x
  have hφ : Test B potential := radial_potential_test
  obtain ⟨K,hφL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφ.2.1 hφ.1 (by simp)
  obtain ⟨C,hq'⟩ := lipschitz_mul_compact (squareQuotient_lipschitz hL he hz) hφL hφ.2.1
  have hq : LipschitzWith C q := by
    simpa only [q,mul_comm] using hq'
  have hc : HasCompactSupport q := hφ.2.1.mul_right
  have hs : tsupport q ⊆ B := tsupport_mul_subset_left.trans hφ.2.2
  have hq0 := setIntegral_gradient_compact hq hc hs e
  have hu0 := SobolevCalculus.gradient_zero_on_zero_set isOpen_ball (LipschitzSobolev.h1_ball hL 0 2)
  have hqz := SobolevCalculus.gradient_zero_on_zero_set isOpen_ball (LipschitzSobolev.h1_ball hq 0 2)
  let F := fun x=>potential x*‖gradient u x‖^2-rawKernel x*u x^2
  let R := fun x=>potential x*‖gradient u x-(u x/inner ℝ x e) • e‖^2
  have hR : R =ᵐ[μ] (fun x=>F x-inner ℝ (gradient q x) e) := by
    filter_upwards [ae_restrict_of_ae hL.ae_differentiableAt,hu0,hqz] with x hx hux hqx
    by_cases ht : 0 < inner ℝ x e
    · dsimp [R,F,q]
      rw [weightedQuotient_directional hx ht he]
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
        real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, he, mul_one, sq_abs, real_inner_comm e (gradient u x)]
      ring
    · have hu : u x=0 := hz x (not_lt.mp ht)
      have hqv : q x=0 := by simp [q,squareQuotient,ht]
      simp only [R,F,hu,hux hu,hqx hqv,zero_div,zero_smul,sub_self,norm_zero,zero_pow (by norm_num : 2≠0),
        mul_zero,inner_zero_left]
  have hFi : Integrable F μ := radial_outer_integrable hL
  have hQi : Integrable (fun x=>inner ℝ (gradient q x) e) μ :=
    (memLp_inner_const (LipschitzSobolev.h1_ball hq 0 2).2.1 e).integrable (by norm_num)
  have hRi : Integrable R μ := (hFi.sub hQi).congr hR.symm
  have hRint : (∫ x, R x ∂μ)=0 := by
    rw [integral_congr_ae hR,integral_sub hFi hQi]
    change (∫ x in B, F x)-(∫ x in B, inner ℝ (gradient q x) e)=0
    rw [radial_outer_identity hm hL hom,hq0,sub_self]
  have haz : R =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall (fun x=>mul_nonneg (potential_nonneg x) (sq_nonneg _))) hRi).mp hRint
  have hle : volume.restrict (ball (0:Space d) 1) ≤ μ :=
    Measure.restrict_mono (ball_subset_ball (by norm_num)) le_rfl
  filter_upwards [ae_mono hle haz,ae_restrict_mem measurableSet_ball] with x hx hxb
  have hsq : ‖gradient u x-(u x/inner ℝ x e) • e‖^2=0 :=
    (mul_eq_zero.mp hx).resolve_left (potential_pos hxb).ne'
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))
end Bernoulli.Halfspace

end
end

end OAI
