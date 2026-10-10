import OAI.Geometry.RCD.Harmonic.FirstOrderMetricLimit
import OAI.Geometry.RCD.Metric.MovingPointedData

namespace OAI

/-! # A metric limit and the actual first-order coordinate limits together

Centers and physical radii may both vary. The metric space and its
approximations are constructed from CD finite nets; the finite coordinate
family is transferred through those same maps. No curvature-dimension or
harmonicity assertion about the limit is assumed here.
-/

open Set Metric Filter MeasureTheory TopologicalSpace
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.first_order_metric_compactness {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    (p : ℕ → X) (r ε : ℕ → ℝ)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*(r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hε0 : Tendsto ε atTop (𝓝 0))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hsplit : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (80*r k) (ε k) (u k) (v k)) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ ∃ (Y : Type u) (dY : MetricSpace Y),
      letI := dY
      ∃ (_ : ProperSpace Y) (q : Y) (δ : ℕ → ℝ) (V : ℕ → X → Y) (g : Fin n → Y → ℝ),
        (∀ k, 0<δ k ∧ δ k≤1) ∧ Tendsto δ atTop (𝓝 0) ∧
        (∀ k, IsPointedApproximation (p (a k)) q (r (a k)) 5 (δ k) (V k)) ∧
        (∀ i, LipschitzWith 2 (g i)) ∧
        ∀ i η, 0<η → ∀ᶠ k in atTop, ∀ x, dist x (p (a k))≤5*r (a k) →
          |(v (a k) x i-v (a k) (p (a k)) i)/r (a k)-g i (V k x)|<η := by
  obtain ⟨a,ha,Y,dY,hproper,q,hconv⟩ := hX.moving_pointed_compactness hn p r hr hcurv
  let := dY
  let := hproper
  obtain ⟨b,V,hb,hV⟩ := hconv.subsequence_data (by norm_num : (0:ℝ)<5)
  let α := a∘b
  have hα : StrictMono α := ha.comp hb
  let δ : ℕ → ℝ := fun k => max (1/((k:ℝ)+1)) (ε (α k))
  have hδ (k : ℕ) : 0<δ k ∧ δ k≤1 := by
    constructor
    · exact (show 0<1/((k:ℝ)+1) by positivity).trans_le (le_max_left _ _)
    · apply max_le
      · apply (div_le_one (by positivity)).mpr
        linarith [Nat.cast_nonneg (α := ℝ) k]
      · exact hε1 (α k)
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ,Function.comp_def,max_self] using tendsto_one_div_add_atTop_nhds_zero_nat.max
      (hε0.comp hα.tendsto_atTop)
  have hVδ (k : ℕ) : IsPointedApproximation (p (α k)) q (r (α k)) 5 (δ k) (V k) :=
    (hV k).mono_error (le_max_left _ _)
  have hsδ (k : ℕ) : FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p (α k)) (80*r (α k)) (δ k) (u (α k)) (v (α k)) :=
    (hsplit (α k)).mono_error _ _ (hε (α k)) (le_max_right _ _)
  obtain ⟨c,hc,g,hg,hvalues⟩ := hX.first_order_metric_value_limit hn q
    (p∘α) (r∘α) δ V (fun k => hr (α k)) (fun k => (hδ k).1.le)
    (fun k => (hδ k).2) hδ0 hVδ (u∘α) (v∘α) hsδ
  exact ⟨α∘c,hα.comp hc,Y,dY,hproper,q,δ∘c,V∘c,g,
    fun k => hδ (c k),hδ0.comp hc.tendsto_atTop,fun k => hVδ (c k),hg,hvalues⟩

end RegularPointCoordinates

end

end OAI
