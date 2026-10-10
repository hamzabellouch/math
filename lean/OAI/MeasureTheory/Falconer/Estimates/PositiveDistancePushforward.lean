import OAI.MeasureTheory.Falconer.Estimates.PositiveDistanceGoodSet
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

structure PositiveDistanceData where
  Q : DyadicSquare
  ρ : Measure Plane
  mass : ℝ → ℝ
  N : ℕ
  q : ℕ
  a : ℕ
  t : ℕ
  lam : ℝ
  sig : ℝ
  J : ℕ
  i : ℕ
  X : CellPath
  Y : CellPath

namespace PositiveDistanceData

noncomputable def good (d : PositiveDistanceData) : Set (Plane × Plane) :=
  positiveDistanceGoodSet d.Q d.ρ d.mass d.N d.q d.a d.t d.lam d.sig d.J d.i

theorem measurable_good (d : PositiveDistanceData) : MeasurableSet d.good :=
  measurable_positiveDistanceGoodSet _ _ _ _ _ _ _ _ _ _ _

noncomputable def cellPair (d : PositiveDistanceData) : Measure (Plane × Plane) :=
  (d.ρ.restrict (d.Q.descendant d.X).carrier).prod
    (d.ρ.restrict (d.Q.descendant d.Y).carrier)

noncomputable def pair (d : PositiveDistanceData) : Measure (Plane × Plane) :=
  d.cellPair.restrict d.good

noncomputable def distance (d : PositiveDistanceData) : Measure ℝ :=
  Measure.map (fun z : Plane × Plane => dist z.1 z.2) d.pair

instance cellPair_finite (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] :
    IsFiniteMeasure d.cellPair := by unfold cellPair; infer_instance

instance pair_finite (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] :
    IsFiniteMeasure d.pair := by unfold pair; infer_instance

instance distance_finite (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] :
    IsFiniteMeasure d.distance := by unfold distance; infer_instance

noncomputable def width (d : PositiveDistanceData) : ℝ := (2:ℝ)^(-(d.t:ℝ))

noncomputable def levelMass (d : PositiveDistanceData) : ℝ :=
  ((2:ℝ)^d.N)^(-d.mass d.a)

noncomputable def normalization (d : PositiveDistanceData) : ℝ≥0∞ :=
  ENNReal.ofReal ((2:ℝ)^((d.t:ℝ)-d.a) / d.levelMass^4)

noncomputable def coincidence (d : PositiveDistanceData) : ℝ≥0∞ :=
  d.normalization * (d.pair.prod d.pair)
    {z | |dist z.1.1 z.1.2 - dist z.2.1 z.2.2| ≤ 100*d.width}

theorem distance_apply (d : PositiveDistanceData) {s : Set ℝ} (hs : MeasurableSet s) :
    d.distance s = d.cellPair {z | dist z.1 z.2 ∈ s ∧ z ∈ d.good} := by
  rw [distance,Measure.map_apply (continuous_fst.dist continuous_snd).measurable hs,
    pair,Measure.restrict_apply ((continuous_fst.dist continuous_snd).measurable hs)]
  rfl

theorem distance_prod (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ] :
    d.distance.prod e.distance = Measure.map
      (fun z : (Plane × Plane) × (Plane × Plane) =>
        (dist z.1.1 z.1.2, dist z.2.1 z.2.2)) (d.pair.prod e.pair) :=
  Measure.map_prod_map _ _ (continuous_fst.dist continuous_snd).measurable
    (continuous_fst.dist continuous_snd).measurable

theorem distance_collision (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] (w : ℝ) :
    (d.distance.prod d.distance) {z : ℝ × ℝ | |z.1-z.2| ≤ w} =
      (d.pair.prod d.pair) {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ w} := by
  rw [distance_prod,Measure.map_apply (by fun_prop) (by measurability)]
  rfl

theorem coincidence_four_point (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] :
    d.coincidence = d.normalization * (d.cellPair.prod d.cellPair)
      {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ 100*d.width ∧
        z.1 ∈ d.good ∧ z.2 ∈ d.good} := by
  rw [coincidence,pair,Measure.prod_restrict,Measure.restrict_apply (by measurability)]
  rfl

theorem lintegral_distance_prod (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z ∂d.distance.prod e.distance) =
      ∫⁻ z, F (dist z.1.1 z.1.2,dist z.2.1 z.2.2) ∂d.pair.prod e.pair := by
  rw [distance_prod,lintegral_map hF (by fun_prop)]

theorem lintegral_drop_extra_restriction (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F)
    (S : Set ((Plane × Plane) × (Plane × Plane))) :
    (∫⁻ z in S, F (dist z.1.1 z.1.2,dist z.2.1 z.2.2) ∂d.pair.prod e.pair) ≤
      ∫⁻ z, F z ∂d.distance.prod e.distance := by
  rw [lintegral_distance_prod d e F hF]
  exact lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)

end PositiveDistanceData

end PlanarFalconer

end OAI
