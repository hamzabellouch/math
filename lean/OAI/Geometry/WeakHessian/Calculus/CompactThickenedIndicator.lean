import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessianCalculus
variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MeasurableSpace X] [BorelSpace X] [TopologicalSpace.SeparableSpace X] in
lemma compact_thickenedIndicator {s : Set X} (hs : IsCompact s) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (fun x => (thickenedIndicator hδ s x : ℝ)) := by
  have hc : IsCompact (Metric.cthickening δ s) := hs.cthickening
  apply hc.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ Metric.isClosed_cthickening
  intro x hx
  apply Metric.thickening_subset_cthickening δ s
  by_contra h
  exact hx (by simp only [thickenedIndicator_zero hδ s h, NNReal.coe_zero])

omit [ProperSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace.SeparableSpace X] in
lemma lipschitz_thickenedIndicator {s : Set X} {δ : ℝ} (hδ : 0 < δ) :
    LipschitzWith δ.toNNReal⁻¹ (fun x => (thickenedIndicator hδ s x : ℝ)) := by
  exact NNReal.isometry_coe.lipschitzWith.comp (lipschitzWith_thickenedIndicator hδ s) |>.weaken
    (by simp)

lemma ae_eq_zero_of_integral_lipschitz_compact {H : X → ℝ}
    (hH : LocallyIntegrable H m)
    (hzero : ∀ φ : X → ℝ, HasCompactSupport φ →
      (∃ L : ℝ≥0, LipschitzWith L φ) → (∫ x, H x * φ x ∂m) = 0) :
    H =ᵐ[m] 0 := by
  apply ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero' hH
  intro s hs
  let δ : ℕ → ℝ := fun n => 1 / (n + 1)
  have hδ : ∀ n, 0 < δ n := fun n => by dsimp only [δ]; positivity
  let φ : ℕ → X → ℝ := fun n x => thickenedIndicator (hδ n) s x
  have hφc : ∀ n, Continuous (φ n) := fun n => (lipschitz_thickenedIndicator (hδ n)).continuous
  have hφzero : ∀ n, (∫ x, H x * φ n x ∂m) = 0 := fun n =>
    hzero _ (compact_thickenedIndicator hs (hδ n)) ⟨_,lipschitz_thickenedIndicator (hδ n)⟩
  have hφbound : ∀ n x, |φ n x| ≤ 1 := by
    intro n x
    simpa only [φ, abs_of_nonneg (NNReal.coe_nonneg _), NNReal.coe_one] using
      (NNReal.coe_le_coe.mpr (thickenedIndicator_le_one (hδ n) s x))
  have hδle : ∀ n, δ n ≤ 1 := fun n => by
    dsimp only [δ]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  let c : Set X := Metric.cthickening 1 s
  have hc : IsCompact c := hs.cthickening
  have hφout : ∀ n x, x ∉ c → φ n x = 0 := by
    intro n x hx
    have hx' : x ∉ Metric.thickening (δ n) s := fun h =>
      hx (Metric.cthickening_mono (hδle n) s (Metric.thickening_subset_cthickening (δ n) s h))
    simp only [φ, thickenedIndicator_zero (hδ n) s hx', NNReal.coe_zero]
  have hlimφ : ∀ x, Tendsto (fun n => φ n x) atTop (𝓝 (s.indicator (fun _ => (1 : ℝ)) x)) := by
    intro x
    have h := (tendsto_pi_nhds.mp
      (thickenedIndicator_tendsto_indicator_closure hδ tendsto_one_div_add_atTop_nhds_zero_nat s)) x
    have h' := NNReal.continuous_coe.continuousAt.tendsto.comp h
    by_cases hx : x ∈ s <;> simpa [hs.isClosed.closure_eq, φ, hx, Function.comp_def] using h'
  have hm : ∀ n, AEStronglyMeasurable (fun x => H x * φ n x) m :=
    fun n => hH.aestronglyMeasurable.mul (hφc n).aestronglyMeasurable
  have hdom : Integrable (c.indicator (fun x => |H x|)) m :=
    (integrable_indicator_iff hc.measurableSet).mpr (by
      change Integrable (fun x => |H x|) (m.restrict c)
      simpa only [Real.norm_eq_abs] using (hH.integrableOn_isCompact hc).norm)
  have hlim := tendsto_integral_of_dominated_convergence (c.indicator (fun x => |H x|)) hm hdom
    (fun n => ae_of_all _ fun x => by
      by_cases hx : x ∈ c
      · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hφbound n x)
      · simp only [hφout n x hx, mul_zero, norm_zero, Set.indicator_of_notMem hx, le_rfl])
    (ae_of_all _ fun x => tendsto_const_nhds.mul (hlimφ x))
  have heq : (fun x => H x * s.indicator (fun _ => (1 : ℝ)) x) = s.indicator H := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [heq, integral_indicator hs.measurableSet] at hlim
  exact (tendsto_nhds_unique (by simpa only [hφzero] using (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))) hlim).symm

end WeakHessianCalculus

end

end OAI
