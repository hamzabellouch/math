import OAI.NumberTheory.TotientAsymptotic.UniformPrefactor
import OAI.NumberTheory.TotientAsymptotic.CollisionScale
import OAI.NumberTheory.TotientAsymptotic.RenewalInput
import OAI.NumberTheory.TotientAsymptotic.RowModelScale

namespace OAI

/-! Elementary lower bounds for the dimension and volume normalization. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma dimension_exponential_lower : ∀ᶠ x : ℝ in atTop,
    Real.exp ((3/5:ℝ)*(m x:ℝ)) ≤ B x := by
  filter_upwards [theta_eventually_mem,
    B_tendsto.eventually (eventually_ge_atTop (Real.exp 1))] with x hθ hB
  have hbpos : 0 < B x := (Real.exp_pos 1).trans_le hB
  have hlogB : 1 ≤ Real.log (B x) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hB
  have hloglog : 0 ≤ Real.log (Real.log (B x)) := Real.log_nonneg hlogB
  have hm : (m x:ℝ) ≤ psi (B x) := by
    have hh := hθ.1
    change 0 ≤ psi (B x)-(m x:ℝ) at hh
    linarith only [hh]
  have hm' := (le_div_iff₀ lam_pos).mp hm
  have hLam := mul_le_mul_of_nonneg_right collision_lambda_bounds.1.le
    (Nat.cast_nonneg (m x) : (0:ℝ) ≤ m x)
  have he : (3/5:ℝ)*(m x:ℝ) ≤ Real.log (B x) := by
    change (m x:ℝ)*lam ≤ Real.log (B x)-Real.log (Real.log (B x)) at hm'
    nlinarith only [hm',hLam,hloglog]
  simpa only [Real.exp_log hbpos] using Real.exp_le_exp.mpr he

lemma central_volume_one_le : ∀ᶠ x : ℝ in atTop,1 ≤ G x (m x) := by
  obtain ⟨J,hJ,hproj⟩ := uniform_projected_volume_bound fordRenewalInput
  have hsmall := ((summable_projectedEnvelope hJ).tendsto_atTop_zero.comp m_tendsto).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hproj,hsmall,B_tendsto.eventually (eventually_gt_atTop (0:ℝ))]
    with x hx hs hB
  change projectedEnvelope J (m x)<1 at hs
  have hp := hx (m x) le_rfl
  rw [Nat.sub_self,show G x 0=1 by simp [G]] at hp
  change 1/G x (m x) ≤ projectedEnvelope J (m x) at hp
  have hh := (div_le_iff₀ (G_pos hB (m x))).mp hp
  have hl := mul_le_mul_of_nonneg_right hs.le (G_pos hB (m x)).le
  linarith only [hh,hl]

lemma dimension_row_model_budget {F : ℝ} (hF : 0 ≤ F) :
    ∀ᶠ x : ℝ in atTop,
      rowMassCutoffHeight F (rowModelDecay (m x))+4 ≤ B x ∧
      (m x:ℝ)^2/4 ≤ rowModelDecay (m x)*B x := by
  have hm : Tendsto (fun x : ℝ => (m x:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp m_tendsto
  have hbud := hm.eventually (row_model_ambient_budget hF)
  filter_upwards [hbud,dimension_exponential_lower] with x hx hb
  exact hx (B x) hb

end TotientAsymptotic

end

end OAI
