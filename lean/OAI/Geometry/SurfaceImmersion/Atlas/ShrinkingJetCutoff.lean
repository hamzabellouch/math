import OAI.Geometry.SurfaceImmersion.Atlas.FlatJetWeightedBound

namespace OAI

/-! Fixed cutoffs rescaled into smaller coordinate balls, with derivative
bounds measured at their actual radius. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def flatJetCutoff : ContDiffBump (0 : Base) := ⟨1/4,1/2,by norm_num,by norm_num⟩
def shrinkingJetCutoff (r : ℝ) (x : Base) : ℝ := flatJetCutoff (r⁻¹ • x)

lemma shrinkingJetCutoff_smooth (r : ℝ) : ContDiff ℝ ∞ (shrinkingJetCutoff r) :=
  flatJetCutoff.contDiff.comp (contDiff_id.const_smul r⁻¹)

lemma shrinkingJetCutoff_germ (r : ℝ) : shrinkingJetCutoff r =ᶠ[𝓝 (0 : Base)] 1 := by
  have hc0 : Continuous (fun x : Base => r⁻¹ • x) := by fun_prop
  have hc : Tendsto (fun x : Base => r⁻¹ • x) (𝓝 0) (𝓝 0) := by
    simpa only [smul_zero] using hc0.continuousAt.tendsto (x := (0 : Base))
  exact flatJetCutoff.eventuallyEq_one.comp_tendsto hc

lemma shrinkingJetCutoff_tsupport {r : ℝ} (hr : 0 < r) :
    tsupport (shrinkingJetCutoff r) ⊆ closedBall (0 : Base) (r/2) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hn
  have hn' : r/2 < ‖x‖ := by
    simpa only [mem_closedBall,dist_zero_right,not_le] using hn
  have hd : flatJetCutoff.rOut ≤ dist (r⁻¹ • x) 0 := by
    change (1/2 : ℝ) ≤ dist (r⁻¹ • x) 0
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hr]
    change (1/2 : ℝ) ≤ r⁻¹*‖x‖
    rw [← div_eq_inv_mul]
    apply (le_div_iff₀ hr).mpr
    linarith
  exact hx (flatJetCutoff.zero_of_le_dist hd)

theorem shrinkingJetCutoff_weighted_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
      WeightedEstimates.WeightedBound (ball (0 : Base) r) r 2 C (shrinkingJetCutoff r) := by
  obtain ⟨C,hC,hb⟩ := flatJetCutoff.hasCompactSupport.exists_bound_iteratedFDeriv
    (𝕜 := ℝ) flatJetCutoff.contDiff 2
  refine ⟨C,hC,?_⟩
  intro r hr j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j isOpen_ball hx]
  change r^j*‖iteratedFDeriv ℝ j (fun y : Base => flatJetCutoff (r⁻¹ • y)) x‖ ≤ C
  have hjc : ContDiff ℝ j (flatJetCutoff : Base → ℝ) := flatJetCutoff.contDiff
  rw [congrFun (iteratedFDeriv_comp_const_smul r⁻¹ hjc) x,norm_smul]
  simp only [Real.norm_eq_abs,abs_pow,abs_inv,abs_of_pos hr,inv_pow]
  rw [← mul_assoc,mul_inv_cancel₀ (pow_ne_zero j (ne_of_gt hr)),one_mul]
  exact hb j hj _

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
