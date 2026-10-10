import OAI.MeasureTheory.Falconer.Radial.RadialTupleTransversality

namespace OAI

/-! # Measurable troublesome pairs use the full original conditional source law -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem measurable_normalized_vector {X : Type*} [MeasurableSpace X]
    {f : X → Space d} (hf : Measurable f) :
    Measurable (fun x => NormedSpace.normalize (f x)) :=
  hf.norm.inv.smul hf

theorem measurable_perpendicular_vectors {X : Type*} [MeasurableSpace X]
    {v z : X → Space d} (hv : Measurable v) (hz : Measurable z) :
    Measurable (fun x => perpendicularPart (v x) (z x)) := by
  have hi : Measurable (fun x => inner ℝ (v x) (z x)) := hv.inner hz
  exact hz.sub (hi.smul hv)

noncomputable def radialTubeMass (μ : Measure (Space d)) (W : ℝ)
    (p : Space d × Space d) : ℝ≥0∞ :=
  μ {y | ‖perpendicularPart (normalize (p.1-p.2)) (y-p.2)‖ ≤ W}

theorem radialTubeMass_measurable (μ : Measure (Space d)) [SFinite μ] (W : ℝ) :
    Measurable (radialTubeMass μ W) := by
  let A : Set ((Space d × Space d) × Space d) :=
    {q | ‖perpendicularPart (normalize (q.1.1-q.1.2)) (q.2-q.1.2)‖ ≤ W}
  have hA : MeasurableSet A := by
    have hv : Measurable (fun q : (Space d × Space d) × Space d =>
        NormedSpace.normalize (q.1.1-q.1.2)) :=
      measurable_normalized_vector (measurable_fst.fst.sub measurable_fst.snd)
    have hy : Measurable (fun q : (Space d × Space d) × Space d => q.2-q.1.2) :=
      measurable_snd.sub measurable_fst.snd
    exact measurableSet_le (measurable_perpendicular_vectors hv hy).norm measurable_const
  exact measurable_measure_prodMk_left hA

noncomputable def troublesomePair (μ : Measure (Space d)) (c : Space d)
    (r D B W : ℝ) (F : ℝ≥0∞) : Set (Space d × Space d) :=
  {p | r ≤ ‖c-p.2‖ ∧ p.1 ≠ p.2 ∧ ‖p.1-c‖ ≤ D ∧ ‖p.1‖ ≤ B ∧ F < radialTubeMass μ W p}

theorem troublesomePair_measurable (μ : Measure (Space d)) [SFinite μ]
    (c : Space d) (r D B W : ℝ) (F : ℝ≥0∞) :
    MeasurableSet (troublesomePair μ c r D B W F) := by
  have h₁ : MeasurableSet {p : Space d × Space d | r ≤ ‖c-p.2‖} :=
    measurableSet_le measurable_const (by fun_prop)
  have h₂ : MeasurableSet {p : Space d × Space d | p.1 ≠ p.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  have h₃ : MeasurableSet {p : Space d × Space d | ‖p.1-c‖ ≤ D} :=
    measurableSet_le (by fun_prop) measurable_const
  have h₄ : MeasurableSet {p : Space d × Space d | ‖p.1‖ ≤ B} :=
    measurableSet_le (by fun_prop) measurable_const
  exact h₁.inter (h₂.inter (h₃.inter (h₄.inter
    (measurableSet_lt measurable_const (radialTubeMass_measurable μ W)))))

end Falconer

end OAI
