import OAI.Geometry.RCD.Heat.HeatVarianceBounded

namespace OAI

/-! # The pointwise reverse Poincaré inequality for bounded L² data -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Finite-measure indicators test a weighted integral without introducing
an abstract duality hypothesis. -/
theorem integral_indicatorConstLp_mul (s : Set X) (hs : MeasurableSet s)
    (hfin : μ s ≠ ∞) (g : X → ℝ) :
    (∫ x, indicatorConstLp 2 hs hfin (1:ℝ) x*g x ∂μ) = ∫ x in s, g x ∂μ := by
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hfin) (c := (1:ℝ))] with x hx
  rw [hx]
  by_cases h : x ∈ s <;> simp [h]

variable [MetricSpace X] [BorelSpace X]

/-- The actual heat flow satisfies reverse Poincaré almost everywhere.
The right side is the heat flow of the actual L² square. -/
theorem NoncollapsedRCD.heat_reverse_poincare
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (p : X) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    let μ := hausdorff n X
    ∀ (f : Lp ℝ 2 μ) (C : ℝ≥0) (hf : ∀ᵐ x ∂μ, |f x| ≤ C) (T : ℝ) (hT : 0 < T),
      ∀ᵐ x ∂μ, 2*T*Real.exp (-2*|K| *T)*
          (SobolevSpace.minimalSlope μ hX.quadratic (heatSobolev μ hX.quadratic T hT f) x)^2+
          (heatAt μ hX.quadratic T f x)^2 ≤
        heatAt μ hX.quadratic T (boundedLpSquare μ f C C.coe_nonneg hf) x := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : μ.Regular := inferInstance
  dsimp only
  intro f C hf T hT
  let A := 2*T*Real.exp (-2*|K| *T)
  let G := SobolevSpace.minimalSlope μ hX.quadratic (heatSobolev μ hX.quadratic T hT f)
  let Q := boundedLpSquare μ f C C.coe_nonneg hf
  have hQrep : Q =ᵐ[μ] fun x => f x^2 := boundedLpSquare_coe μ f C C.coe_nonneg hf
  have hQi : Integrable Q μ := (Lp.memLp f).integrable_sq.congr hQrep.symm
  have hR : Integrable (heatAt μ hX.quadratic T Q) μ := heatAt_integrable μ hX.quadratic T Q hQi
  have hL : Integrable (fun x => A*G x^2+(heatAt μ hX.quadratic T f x)^2) μ :=
    ((Lp.memLp G).integrable_sq.const_mul A).add (Lp.memLp (heatAt μ hX.quadratic T f)).integrable_sq
  apply ae_le_of_forall_setIntegral_le hL hR
  intro s hs hfin
  let w : Lp ℝ 2 μ := indicatorConstLp 2 hs hfin.ne 1
  have hwrep : w =ᵐ[μ] s.indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
  have hw0 : 0 ≤ w := by
    apply (Lp.coeFn_nonneg _).mp
    filter_upwards [hwrep] with x hx
    rw [hx]
    by_cases h : x ∈ s <;> simp [h]
  have hwb : ∀ᵐ x ∂μ, |w x| ≤ (1:ℝ≥0) := by
    filter_upwards [hwrep] with x hx
    rw [hx]
    by_cases h : x ∈ s <;> simp [h]
  have hv := hX.heat_variance_lower_bounded K n hn p f w C 1 hf hw0 hwb T hT
  have hr : (∫ x, heatAt μ hX.quadratic T w x*f x^2 ∂μ) =
      ∫ x in s, heatAt μ hX.quadratic T Q x ∂μ := by
    calc
      _ = inner ℝ (heatAt μ hX.quadratic T w) Q := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hQrep] with x hx
        simp only [Real.inner_apply,hx]
      _ = inner ℝ w (heatAt μ hX.quadratic T Q) := heatAt_inner μ hX.quadratic T w Q
      _ = ∫ x, w x*heatAt μ hX.quadratic T Q x ∂μ := by
        rw [L2.inner_def]
        simp only [Real.inner_apply]
      _ = _ := integral_indicatorConstLp_mul μ s hs hfin.ne _
  rw [hr,integral_indicatorConstLp_mul μ s hs hfin.ne,
    integral_indicatorConstLp_mul μ s hs hfin.ne] at hv
  rw [integral_add ((Lp.memLp G).integrable_sq.const_mul A).integrableOn
    (Lp.memLp (heatAt μ hX.quadratic T f)).integrable_sq.integrableOn,integral_const_mul]
  linarith

end RegularPointCoordinates

end

end OAI
