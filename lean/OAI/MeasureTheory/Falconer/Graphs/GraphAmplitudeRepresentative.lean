import OAI.MeasureTheory.Falconer.Graphs.GraphCompleteWeightSupport
import OAI.MeasureTheory.Falconer.Graphs.GraphAmplitudeSupport

namespace OAI

namespace PlanarFalconer
open Set

theorem graph_directions_chartZ (φ z : ℝ) :
    graphChartZ (sourceDirection (φ+Real.arctan z)) (sourceDirection (φ-Real.arctan z)) = z := by
  let u := sourceDirection (φ+Real.arctan z)
  let v := sourceDirection (φ-Real.arctan z)
  have hn : 0 < ‖u+v‖ := by rw [graph_directions_sum_norm]; positivity
  have hd := graph_chart_difference u v (norm_sourceDirection _) (norm_sourceDirection _) (norm_pos_iff.mp hn)
  have he : u-v = z • quarterTurn (u+v) := by
    dsimp [u,v]
    rw [graph_directions_sum, quarterTurn_smul, sourceDirection_add_arctan, sourceDirection_sub_arctan]
    module
  have hq : quarterTurn (u+v) ≠ 0 := by rw [← norm_ne_zero_iff,graph_quarterTurn_norm]; exact hn.ne'
  exact (smul_left_injective ℝ hq) (hd.symm.trans he)

theorem graph_directions_chartAxis (φ z : ℝ) :
    graphChartAxis (sourceDirection (φ+Real.arctan z)) (sourceDirection (φ-Real.arctan z)) = sourceDirection φ := by
  rw [graphChartAxis, graph_directions_sum_norm, graph_directions_sum, smul_smul,
    inv_mul_cancel₀ (by positivity : (2:ℝ)/Real.sqrt (1+z^2) ≠ 0), one_smul]

noncomputable def graphSourceEndpoints (distance plus : Bool) (p : Plane × ℝ) : UnitCircle × UnitCircle :=
  (sourceUnitDirection (graphPlaneAngle p.1+Real.arctan p.2),
    sourceUnitDirection (graphPlaneAngle p.1-Real.arctan p.2+graphSourceChartAxis distance plus))

theorem graphSourceEndpoints_signed (distance plus : Bool) (p : Plane × ℝ) :
    graphSourceSign distance plus • ((graphSourceEndpoints distance plus p).2:Plane) =
      sourceDirection (graphPlaneAngle p.1-Real.arctan p.2) := by
  cases distance <;> cases plus <;>
    simp [graphSourceEndpoints,graphSourceSign,graphSourceChartAxis,sourceUnitDirection,sourceDirection_add_pi]

theorem graphSourceEndpoints_coordinates (distance plus : Bool) {p : Plane × ℝ} (hp : p.1 ≠ 0) :
    graphChartZ ((graphSourceEndpoints distance plus p).1:Plane)
        (graphSourceSign distance plus • ((graphSourceEndpoints distance plus p).2:Plane)) = p.2 ∧
    graphChartAxis ((graphSourceEndpoints distance plus p).1:Plane)
        (graphSourceSign distance plus • ((graphSourceEndpoints distance plus p).2:Plane)) = graphNormalizedAxis p.1 := by
  rw [graphSourceEndpoints_signed]
  change graphChartZ (sourceDirection _) _ = _ ∧ graphChartAxis (sourceDirection _) _ = _
  rw [graph_directions_chartZ, graph_directions_chartAxis,graphNormalizedAxis_eq_all hp]
  exact ⟨rfl,rfl⟩

theorem graphAmplitudePullback_weight_nonzero (b : Fin 4 → Plane → UnitCircle → ℂ)
    (x : Fin 4 → Plane) (distance plus : Bool) (axis δ : ℝ) (j k : ℕ)
    (Ψ : ℝ → ℝ) {p : Plane × ℝ}
    (hp : graphAmplitudePullback b x distance plus axis δ j k Ψ p ≠ 0) :
    graphSourceWeight distance plus axis (angularBinCount δ) j k (graphSourceEndpoints distance plus p) ≠ 0 := by
  intro hz
  apply hp
  change graphSourceWeight distance plus axis (angularBinCount δ) j k
    (sourceUnitDirection (graphPlaneAngle p.1+Real.arctan p.2),
      sourceUnitDirection (graphPlaneAngle p.1-Real.arctan p.2+graphSourceChartAxis distance plus)) = 0 at hz
  simp [graphAmplitudePullback,graphFourAmplitude,hz]

def GraphSourceRepresentative (distance plus : Bool) (axis δ : ℝ) (j k : ℕ)
    (q : UnitCircle × UnitCircle) : Prop :=
  q ∈ tsupport (graphSourceWeight distance plus axis (angularBinCount δ) j k) ∧
    ∀ w ∈ tsupport (graphSourceWeight distance plus axis (angularBinCount δ) j k),
    |graphChartZ (w.1:Plane) (graphSourceSign distance plus • (w.2:Plane))-
      graphChartZ (q.1:Plane) (graphSourceSign distance plus • (q.2:Plane))|+
    dist (graphChartAxis (w.1:Plane) (graphSourceSign distance plus • (w.2:Plane)))
      (graphChartAxis (q.1:Plane) (graphSourceSign distance plus • (q.2:Plane))) ≤ 112*δ

theorem graphSourceRepresentative_exists {δ : ℝ} (hδ : 0 < δ) (hcap : δ ≤ 2*Real.pi)
    (distance plus : Bool) (axis : ℝ) (j k : ℕ)
    (hS : (tsupport (graphSourceWeight distance plus axis (angularBinCount δ) j k)).Nonempty) :
    ∃ q, GraphSourceRepresentative distance plus axis δ j k q :=
  graphSourceWeight_complete_representative hδ hcap distance plus axis j k hS

theorem GraphSourceRepresentative.amplitude_coordinates
    {distance plus : Bool} {axis δ : ℝ} {j k : ℕ} {q : UnitCircle × UnitCircle}
    (hq : GraphSourceRepresentative distance plus axis δ j k q)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (x : Fin 4 → Plane)
    {Ψ : ℝ → ℝ} (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {p : Plane × ℝ} (hp : graphAmplitudePullback b x distance plus axis δ j k Ψ p ≠ 0) :
    |p.2-graphChartZ (q.1:Plane) (graphSourceSign distance plus • (q.2:Plane))|+
      dist (graphNormalizedAxis p.1) (graphChartAxis (q.1:Plane) (graphSourceSign distance plus • (q.2:Plane))) ≤ 112*δ := by
  have hs := graphAmplitudePullback_tsupport b x distance plus axis δ j k hsupp (subset_closure hp)
  have hlo : (1:ℝ)/8 ≤ ‖p.1‖ := hs.2
  have hn : p.1 ≠ 0 := norm_pos_iff.mp (by linarith)
  have hw := hq.2 _ (subset_closure (graphAmplitudePullback_weight_nonzero b x distance plus axis δ j k Ψ hp))
  rw [(graphSourceEndpoints_coordinates distance plus hn).1,
    (graphSourceEndpoints_coordinates distance plus hn).2] at hw
  exact hw

theorem graphAmplitudePullback_zero_of_empty_weight_support
    (b : Fin 4 → Plane → UnitCircle → ℂ) (x : Fin 4 → Plane)
    (distance plus : Bool) (axis δ : ℝ) (j k : ℕ) (Ψ : ℝ → ℝ)
    (hS : ¬(tsupport (graphSourceWeight distance plus axis (angularBinCount δ) j k)).Nonempty) :
    graphAmplitudePullback b x distance plus axis δ j k Ψ = 0 := by
  funext p
  by_contra hp
  exact hS ⟨_,subset_closure (graphAmplitudePullback_weight_nonzero b x distance plus axis δ j k Ψ hp)⟩

end PlanarFalconer

end OAI
