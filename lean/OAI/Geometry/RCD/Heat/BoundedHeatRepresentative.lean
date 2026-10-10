import OAI.Geometry.RCD.Heat.HeatBoundedSmoothing

namespace OAI

/-! # Canonical bounded-data heat representatives

The actual Cheeger semigroup and the proved reverse Poincare estimate give
continuous representatives on every RCD space in this application. Full
support makes the representative unique; positivity, linearity and the
Markov amplitude bound therefore hold at every point. No heat kernel is
assumed in this construction.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X)

/-- Essential boundedness of the L² datum; only a finite amplitude is used. -/
def HasBoundedAmplitude (f : Lp ℝ 2 (hausdorff n X)) : Prop :=
  ∃ C : ℝ≥0, ∀ᵐ x ∂hausdorff n X, |f x| ≤ C

namespace NoncollapsedRCD

variable [ProperSpace X] [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

/-- The continuous representative constructed from bounded-data smoothing. -/
def boundedHeat (f : Lp ℝ 2 (hausdorff n X)) (hf : HasBoundedAmplitude f)
    (t : ℝ) (ht : 0 < t) : X → ℝ :=
  (hX.heat_bounded_lipschitz K n hn p f hf.choose hf.choose_spec t ht).choose

omit [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] in
theorem boundedHeat_represents (f : Lp ℝ 2 (hausdorff n X))
    (hf : HasBoundedAmplitude f) (t : ℝ) (ht : 0 < t) :
    heatAt (hausdorff n X) hX.quadratic t f =ᵐ[hausdorff n X]
      hX.boundedHeat hn p f hf t ht :=
  (hX.heat_bounded_lipschitz K n hn p f hf.choose hf.choose_spec t ht).choose_spec.2

omit [ProperSpace X] [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)]
  [(hausdorff n X).Regular] in
theorem boundedHeat_continuous (f : Lp ℝ 2 (hausdorff n X))
    (hf : HasBoundedAmplitude f) (t : ℝ) (ht : 0 < t) :
    Continuous (hX.boundedHeat hn p f hf t ht) :=
  (hX.heat_bounded_lipschitz K n hn p f hf.choose hf.choose_spec t ht).choose_spec.1.continuous

omit [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] in
/-- Independence of the base point and the bound chosen in the construction. -/
theorem boundedHeat_unique (f : Lp ℝ 2 (hausdorff n X))
    (hf : HasBoundedAmplitude f) (t : ℝ) (ht : 0 < t)
    {v : X → ℝ} (hv : Continuous v)
    (hrep : heatAt (hausdorff n X) hX.quadratic t f =ᵐ[hausdorff n X] v) :
    hX.boundedHeat hn p f hf t ht = v := by
  let := hX.openPos K n
  exact MeasureTheory.Measure.eq_of_ae_eq ((hX.boundedHeat_represents hn p f hf t ht).symm.trans hrep)
    (hX.boundedHeat_continuous hn p f hf t ht) hv

omit [ProperSpace X] [(hausdorff n X).Regular] in
theorem boundedHeat_lipschitz (f : Lp ℝ 2 (hausdorff n X))
    (hf : HasBoundedAmplitude f) (t : ℝ) (ht : 0 < t)
    (C : ℝ≥0) (hC : ∀ᵐ x ∂hausdorff n X, |f x| ≤ C) :
    LipschitzWith ⟨Real.sqrt ((C:ℝ)^2/(2*t*Real.exp (-2*|K| *t))),Real.sqrt_nonneg _⟩
      (hX.boundedHeat hn p f hf t ht) := by
  let : ProperSpace X := hX.proper K n hn
  let : (hausdorff n X).Regular := inferInstance
  obtain ⟨v, hv, hrep⟩ := hX.heat_bounded_lipschitz K n hn p f C hC t ht
  rw [hX.boundedHeat_unique hn p f hf t ht hv.continuous hrep]
  exact hv

end NoncollapsedRCD
end RegularPointCoordinates

end

end OAI
