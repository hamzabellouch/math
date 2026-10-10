import OAI.Probability.SLE.Mass.LevelConditionalMean

namespace OAI

/-! Convex tail averages of current conditional mean measures have the
same signed compact-test limit as the original radius levels. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

theorem convexCurrentMean_test_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hmono : Monotone u)
    (hlim : Tendsto u atTop atTop) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (hw₀ : ∀ n i, i ∈ s n → 0 ≤ w n i) (hw₁ : ∀ n, ∑ i ∈ s n, w n i = 1)
    (t : ℝ≥0) (E : Set Ω) (f : C_c(upperHalfPlane,ℝ)) :
    Tendsto (fun n => ∫ z, f z ∂convexCurrentMean (P.restrict E) κ B γ G u s w n t)
      atTop (𝓝 (∫ z, f z ∂(P.restrict E).bind (halfPlaneGreenMeasure κ B γ G t))) := by
  let ρ := initialGreenMeasure κ
  let : IsFiniteMeasureOnCompacts ρ := initialGreenMeasure_finite_on_compacts κ
  let μ (j : ℕ) := (P.restrict E).bind (halfPlaneCurrentMeasure κ B γ G (u j) t)
  have hμ (j : ℕ) : μ j ≤ ρ :=
    (bind_mono_of_measurable (P.restrict E)
      (halfPlaneCurrentMeasure_measurable hBm hBc κ (u j) (hu j) γ G F hw t)
      (halfPlaneGreenMeasure_measurable hBm hBc κ γ G F hw t)
      (fun ω => halfPlaneCurrentMeasure_le_green ω (hw ω) (u j) t)).trans
      (halfPlaneGreenMeasure_mean_le hB hBm hBc hB0 hκ hκ8 γ G F hw t E)
  have hfi (j : ℕ) : Integrable f (μ j) := f.integrable.mono_measure (hμ j)
  have he (n : ℕ) : (∫ z, f z ∂convexCurrentMean (P.restrict E) κ B γ G u s w n t) =
      ∑ i ∈ s n, w n i * (∫ z, f z ∂μ (n+i)) := by
    have hi (i : ℕ) : Integrable f (ENNReal.ofReal (w n i) • μ (n+i)) :=
      (hfi (n+i)).smul_measure ENNReal.ofReal_ne_top
    rw [convexCurrentMean,integral_finsetSum_measure (fun i _ => hi i)]
    apply Finset.sum_congr rfl
    intro i his
    rw [integral_smul_measure,ENNReal.toReal_ofReal (hw₀ n i his),smul_eq_mul]
  simp only [he]
  exact real_convex_tail_tendsto (fun j => ∫ z, f z ∂μ j)
    (halfPlaneCurrentMeasure_mean_test_tendsto hB hBm hBc hB0 hκ hκ8 γ G F hw
      u hu hmono hlim t E f) s w hw₀ hw₁

end SLEExactGauge.Multipoint

end

end OAI
