import OAI.Geometry.RCD.Metric.PointedInnerNeighborhood
import OAI.Geometry.RCD.Metric.FiniteMetricValues

namespace OAI

/-! # A supporting functional transfers through the actual uniform value limits -/

open Set Filter Metric
open scoped Topology InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem limit_support_transfer {q y : Y} {n : ℕ}
    (p z : ℕ → X) (r : ℕ → ℝ) (V : ℕ → X → Y)
    (v : ℕ → X → Euclidean n) (F : Y → Euclidean n)
    (hr : ∀ k, 0<r k) (hF : Continuous F)
    (hVy : Tendsto (fun k => V k (z k)) atTop (𝓝 y))
    (hvalues : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ x, dist x (p k)≤5*r k →
      dist ((r k)⁻¹ • (v k x-v k (p k))) (F (V k x))≤η)
    {c : ℝ} (hinner : ∀ᶠ k in atTop,
      dist (z k) (p k)≤5*r k ∧ ∀ x∈ball (z k) (c*r k/48),
        dist x (p k)≤5*r k ∧ V k x∈closedBall q (1/256))
    (a : Euclidean n) (ha : ‖a‖=1)
    (hsupport : ∀ x∈closedBall q (1/256), ⟪F x-F y,a⟫_ℝ≤0) :
    ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ x∈ball (z k) (c*r k/48),
      ⟪v k x-v k (z k),a⟫_ℝ≤η*r k := by
  intro η hη
  have hlim := (hF.tendsto y).comp hVy
  filter_upwards [hinner,hvalues (η/4) (by positivity),
    Metric.tendsto_nhds.mp hlim (η/4) (by positivity)] with k hk hv hcenter
  intro x hx
  change dist (F (V k (z k))) (F y)<η/4 at hcenter
  obtain ⟨hxp,hxV⟩ := hk.2 x hx
  let w : X → Euclidean n := fun x => (r k)⁻¹ • (v k x-v k (p k))
  have hex := hv x hxp
  have hez := hv (z k) hk.1
  have hzerr : dist (w (z k)) (F y)≤η/2 := by
    have ht := dist_triangle (w (z k)) (F (V k (z k))) (F y)
    change dist (w (z k)) (F (V k (z k)))≤η/4 at hez
    linarith
  have hp := hsupport (V k x) hxV
  have heq : ⟪w x-w (z k),a⟫_ℝ =
      ⟪w x-F (V k x),a⟫_ℝ+⟪F (V k x)-F y,a⟫_ℝ+⟪F y-w (z k),a⟫_ℝ := by
    simp only [inner_sub_left]
    ring
  have hb : ⟪w x-w (z k),a⟫_ℝ≤η := by
    rw [heq]
    have h1 := real_inner_le_norm (w x-F (V k x)) a
    have h2 := real_inner_le_norm (F y-w (z k)) a
    rw [ha,mul_one,← dist_eq_norm] at h1 h2
    rw [dist_comm (F y)] at h2
    linarith
  have hw : w x-w (z k)=(r k)⁻¹ • (v k x-v k (z k)) := by
    dsimp [w]
    rw [← smul_sub]
    congr 1
    abel
  rw [hw,real_inner_smul_left] at hb
  have hrk := hr k
  have hb' := mul_le_mul_of_nonneg_left hb hrk.le
  simpa only [mul_inv_cancel_left₀ hrk.ne',mul_comm η] using hb'

end RegularPointCoordinates

end

end OAI
