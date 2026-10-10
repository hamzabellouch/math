import Mathlib
import OAI.Geometry.WeakHessian.Model
import OAI.Geometry.WeakHessian.LocalBounds.SetDensities

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile123
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
variable {m : Measure X}

lemma lipschitz_point_pairing_bound {g : X → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (u q : Lp ℝ 2 m) (he : g =ᵐ[m] u)
    (hq : Integrable (q : X → ℝ) m) (hqn : ∀ᵐ y ∂m,0 ≤ q y)
    (hqm : ∫ y,q y ∂m = 1) (x : X) {r : ℝ} (hr : 0 ≤ r)
    (hqs : ∀ᵐ y ∂m,r < dist y x → q y = 0) :
    |g x-⟪u,q⟫_ℝ| ≤ (L:ℝ)*r := by
  have hg2 : MemLp g 2 m := (memLp_congr_ae he).mpr (Lp.memLp u)
  have hi1 : Integrable (fun y => q y*g x) m := hq.mul_const _
  have hi2 : Integrable (fun y => q y*g y) m := (Lp.memLp q).integrable_mul hg2
  have hei : (∫ y,q y*g y ∂m) = ⟪u,q⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [he] with y hy
    simp only [RCLike.inner_apply,conj_trivial,hy]
  have hi : Integrable (fun y => q y*g x-q y*g y) m := hi1.sub hi2
  have hh : (∫ y,q y*g x-q y*g y ∂m) = g x-⟪u,q⟫_ℝ := by
    rw [integral_sub hi1 hi2,integral_mul_const,hqm,hei,one_mul]
  rw [← hh]
  calc
    |∫ y,q y*g x-q y*g y ∂m| ≤ ∫ y,|q y*g x-q y*g y| ∂m := abs_integral_le_integral_abs
    _ ≤ ∫ y,q y*((L:ℝ)*r) ∂m := by
      apply integral_mono_ae hi.norm (hq.mul_const _)
      filter_upwards [hqn,hqs] with y hn hs
      change |q y*g x-q y*g y| ≤ _
      rw [← mul_sub,abs_mul,abs_of_nonneg hn]
      by_cases hb : dist y x ≤ r
      · simpa only [mul_comm] using mul_le_mul ((show |g x-g y| ≤ (L:ℝ)*dist y x by
          simpa only [Real.dist_eq,dist_comm] using hg.dist_le_mul x y).trans
          (mul_le_mul_of_nonneg_left hb L.coe_nonneg)) (le_refl (q y)) hn
          (mul_nonneg L.coe_nonneg hr)
      · simp only [hs (lt_of_not_ge hb),zero_mul,le_refl]
    _ = (L:ℝ)*r := by rw [integral_mul_const,hqm,one_mul]

omit [MetricSpace X] in
lemma setDensity_integrable (S : Set X) (hS : MeasurableSet S) (hfin : m S ≠ ∞) :
    Integrable (setDensity S hS hfin : X → ℝ) m := by
  apply Integrable.congr _ (setDensity_coe S hS hfin).symm
  exact (integrableOn_const (C := (m S).toReal⁻¹) hfin).integrable_indicator hS

lemma lipschitz_point_tendsto_of_L2 [BorelSpace X] {ι : Type*} {l : Filter ι}
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    {gs : ι → X → ℝ} {g : X → ℝ} {L M : ℝ≥0}
    (hg : ∀ i,LipschitzWith L (gs i)) (hg0 : LipschitzWith M g)
    (us : ι → Lp ℝ 2 m) (u : Lp ℝ 2 m)
    (he : ∀ i,gs i =ᵐ[m] us i) (he0 : g =ᵐ[m] u)
    (ht : Tendsto us l (𝓝 u)) (x : X) :
    Tendsto (fun i => gs i x) l (𝓝 (g x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let r := ε/(4*((L:ℝ)+(M:ℝ)+1))
  have hr : 0 < r := by dsimp [r]; positivity
  have hm : m (Metric.closedBall x r) ≠ ∞ := ne_of_lt (hfin _ Metric.isBounded_closedBall)
  have hp : m (Metric.closedBall x r) ≠ 0 := ne_of_gt
    ((hfull _ Metric.isOpen_ball ⟨x,Metric.mem_ball_self hr⟩).trans_le (measure_mono Metric.ball_subset_closedBall))
  let q := setDensity (Metric.closedBall x r) Metric.isClosed_closedBall.measurableSet hm
  have hq := setDensity_integrable _ Metric.isClosed_closedBall.measurableSet hm
  have hqn := setDensity_nonneg _ Metric.isClosed_closedBall.measurableSet hm
  have hqm := setDensity_mass _ Metric.isClosed_closedBall.measurableSet hm hp
  have hqs := setDensity_supported _ Metric.isClosed_closedBall.measurableSet hm x (Subset.refl _)
  have Ht : Tendsto (fun i => ⟪us i,q⟫_ℝ) l (𝓝 ⟪u,q⟫_ℝ) := ht.inner tendsto_const_nhds
  filter_upwards [Metric.tendsto_nhds.mp Ht (ε/2) (half_pos hε)] with i hi
  rw [Real.dist_eq] at hi ⊢
  have H1 := lipschitz_point_pairing_bound (hg i) (us i) q (he i) hq hqn hqm x hr.le hqs
  have H2 := lipschitz_point_pairing_bound hg0 u q he0 hq hqn hqm x hr.le hqs
  have H3 : |gs i x-g x| ≤ |gs i x-⟪us i,q⟫_ℝ|+|⟪us i,q⟫_ℝ-⟪u,q⟫_ℝ|+|g x-⟪u,q⟫_ℝ| := by
    have HH := abs_add_le (gs i x-⟪us i,q⟫_ℝ) (⟪us i,q⟫_ℝ-g x)
    have HH2 := abs_sub_le ⟪us i,q⟫_ℝ ⟪u,q⟫_ℝ (g x)
    rw [abs_sub_comm ⟪u,q⟫_ℝ (g x)] at HH2
    ring_nf at HH
    linarith
  have hsmall : ((L:ℝ)+(M:ℝ))*r < ε/2 := by
    dsimp [r]
    have hp : 0 < 4*((L:ℝ)+(M:ℝ)+1) := by positivity
    apply (lt_div_iff₀ (show (0:ℝ)<2 by norm_num)).mpr
    field_simp
    nlinarith [L.coe_nonneg,M.coe_nonneg]
  linarith
end WeakHessian

end
end InlinedFile123

end OAI
