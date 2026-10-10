import OAI.Analysis.CircleDomains.Probability.RandomShifts

namespace OAI

/-!+# Expected wedges for a finite family of actual random staircases

The product space has one uniform shift per coordinate. Distinct labels
have the two-shift law used in the analytic mean calculation.
-/

open MeasureTheory Set Finset

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def staircaseCovector (h δ χ θ x : ℝ) (u c : ℝ × ℝ) : ℝ × ℝ :=
  ((1 - χ) + χ * deriv (shiftedStaircase h δ θ) x) • u +
    (shiftedStaircase h δ θ x - x) • c

theorem continuous_staircaseCovector {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4)
    (χ x : ℝ) (u c : ℝ × ℝ) :
    Continuous (fun θ => staircaseCovector h δ χ θ x u c) := by
  unfold staircaseCovector
  exact ((continuous_const.add
    (continuous_const.mul (continuous_shiftedStaircase_deriv hh hδ hδh x))).smul
    continuous_const).add
    (((continuous_shiftedStaircase_value hh hδ hδh x).sub continuous_const).smul
      continuous_const)

theorem expected_grid_pair_wedge_le {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (u v c : ℝ × ℝ) (x y : ℝ) {h δ χ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4) (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1) :
    (∫ θ, |planarWedge
      (staircaseCovector h δ χ (θ i) x u c)
      (staircaseCovector h δ χ (θ j) y v c)|
        ∂Measure.pi (fun _ : Fin n => shiftLaw h)) ≤
      |planarWedge u v| + h * (|planarWedge u c| + |planarWedge c v|) := by
  let : IsProbabilityMeasure (shiftLaw h) := shiftLaw_isProbabilityMeasure hh
  let f : ℝ × ℝ → ℝ := fun z => |planarWedge
    (staircaseCovector h δ χ z.1 x u c) (staircaseCovector h δ χ z.2 y v c)|
  have hf : Continuous f := by
    have hu : Continuous (fun z : ℝ × ℝ => staircaseCovector h δ χ z.1 x u c) :=
      (continuous_staircaseCovector hh hδ hδh χ x u c).comp continuous_fst
    have hv : Continuous (fun z : ℝ × ℝ => staircaseCovector h δ χ z.2 y v c) :=
      (continuous_staircaseCovector hh hδ hδh χ y v c).comp continuous_snd
    exact ((hu.fst.mul hv.snd).sub (hu.snd.mul hv.fst)).abs
  change (∫ θ, f (θ i, θ j) ∂Measure.pi (fun _ : Fin n => shiftLaw h)) ≤ _
  rw [integral_grid_pair (shiftLaw h) hij f hf.aestronglyMeasurable,
    integral_shiftLaw_pair]
  exact average_staircase_wedge_le u v c x y hh hδ hδh hχ0 hχ1

/-- Fubini turns the pointwise mean estimate into the spatial wedge
estimate. Joint integrability is exposed so this can be used both on
compact smooth pieces and on exhausted finite-energy regions. -/
theorem expected_integrated_grid_pair_wedge_le
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (u v c : X → ℝ × ℝ) (x y χ : X → ℝ) {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hjoint : Integrable (fun p : (ℝ × ℝ) × X =>
      |planarWedge
        (staircaseCovector h δ (χ p.2) p.1.1 (x p.2) (u p.2) (c p.2))
        (staircaseCovector h δ (χ p.2) p.1.2 (y p.2) (v p.2) (c p.2))|)
      (((shiftLaw h).prod (shiftLaw h)).prod μ))
    (hbound : Integrable (fun z => |planarWedge (u z) (v z)| +
      h * (|planarWedge (u z) (c z)| + |planarWedge (c z) (v z)|)) μ) :
    (∫ θ, (∫ z, |planarWedge
      (staircaseCovector h δ (χ z) (θ i) (x z) (u z) (c z))
      (staircaseCovector h δ (χ z) (θ j) (y z) (v z) (c z))| ∂μ)
        ∂Measure.pi (fun _ : Fin n => shiftLaw h)) ≤
      ∫ z, |planarWedge (u z) (v z)| +
        h * (|planarWedge (u z) (c z)| + |planarWedge (c z) (v z)|) ∂μ := by
  let : IsProbabilityMeasure (shiftLaw h) := shiftLaw_isProbabilityMeasure hh
  let f : (ℝ × ℝ) → X → ℝ := fun θ z => |planarWedge
    (staircaseCovector h δ (χ z) θ.1 (x z) (u z) (c z))
    (staircaseCovector h δ (χ z) θ.2 (y z) (v z) (c z))|
  change (∫ θ, (∫ z, f (θ i, θ j) z ∂μ)
    ∂Measure.pi (fun _ : Fin n => shiftLaw h)) ≤ _
  rw [integral_grid_pair (shiftLaw h) hij (fun θ => ∫ z, f θ z ∂μ)
    hjoint.integral_prod_left.aestronglyMeasurable]
  rw [integral_integral_swap hjoint]
  apply integral_mono hjoint.integral_prod_right hbound
  intro z
  change (∫ θ, f θ z ∂(shiftLaw h).prod (shiftLaw h)) ≤
    |planarWedge (u z) (v z)| +
      h * (|planarWedge (u z) (c z)| + |planarWedge (c z) (v z)|)
  rw [integral_shiftLaw_pair]
  exact average_staircase_wedge_le (u z) (v z) (c z) (x z) (y z)
    hh hδ hδh (hχ0 z) (hχ1 z)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
