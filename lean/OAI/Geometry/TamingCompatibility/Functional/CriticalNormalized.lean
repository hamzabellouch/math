import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.UniformScaledJet

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter LineDeriv Set
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma rescaleSchwartz_support (p : E) {r R : ℝ} (hr : 0 < r) (f : 𝓢(E,F))
    (hs : tsupport f ⊆ Metric.ball p (r*R)) :
    tsupport (rescaleSchwartz p r hr.ne' f) ⊆ Metric.ball 0 R := by
  have hpre : tsupport (rescaleSchwartz p r hr.ne' f) ⊆
      (fun x : E => r • x+p) ⁻¹' tsupport f := by
    apply closure_minimal ?_ ((isClosed_tsupport _).preimage ((continuous_const.smul continuous_id).add_const p))
    intro x hx
    apply subset_tsupport f
    change f (r • x+p) ≠ 0
    simpa only [Function.mem_support,rescaleSchwartz_apply] using hx
  intro x hx
  have h := hs (hpre hx)
  rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_right,norm_smul,Real.norm_eq_abs,abs_of_pos hr] at h
  rw [Metric.mem_ball,dist_zero_right]
  nlinarith

theorem normalized_source_Hnat (n : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : E) (r M : ℝ) (hr : 0 < r), 0 ≤ M →
      ∀ f : 𝓢(E,F), tsupport f ⊆ Metric.ball p (r*R) →
      (∀ k ≤ n, ∀ m : Fin k → E, (∀ i, ‖m i‖ ≤ 1) → ∀ x, ‖(∂^{m} f) x‖ ≤ M / r^k) →
      ‖schwartzToH n (r^2 • rescaleSchwartz p r hr.ne' f)‖ ≤ C*M*r^2 := by
  obtain ⟨C,hC,hbound⟩ := schwartz_Hnat_support_bound (E := E) (F := F) n R
  refine ⟨C,hC,fun p r M hr hM f hs hb => ?_⟩
  have hsupport : tsupport (r^2 • rescaleSchwartz p r hr.ne' f) ⊆ Metric.ball 0 R :=
    (tsupport_smul_subset_right (fun _ : E => r^2) (rescaleSchwartz p r hr.ne' f)).trans
      (rescaleSchwartz_support p hr f hs)
  have hder : ∀ k ≤ n, ∀ m : Fin k → E, (∀ i, ‖m i‖ ≤ 1) → ∀ x,
      ‖(∂^{m} (r^2 • rescaleSchwartz p r hr.ne' f)) x‖ ≤ M*r^2 := by
    intro k hk m hm x
    rw [iteratedLineDerivOp_smul,rescaleSchwartz_iterated]
    simp only [smul_apply,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hr.le 2),abs_of_nonneg (pow_nonneg hr.le k),rescaleSchwartz_apply]
    calc
      r^2 * (r^k * ‖(∂^{m} f) (r • x+p)‖) ≤ r^2 * (r^k * (M/r^k)) := by
        gcongr; exact hb k hk m hm _
      _ = M*r^2 := by field_simp
  exact (hbound _ (M*r^2) (by positivity) hsupport hder).trans_eq (by ring)

end TamingCompatibility.HilbertSobolev

end

end OAI
