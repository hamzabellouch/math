import Mathlib

namespace OAI

namespace PlanarL1

/-- A topological drawing by simple plane arcs, with injective vertex placement,
no vertex in an edge interior, and disjoint interiors for distinct unoriented edges. -/
def IsPlanar {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (point : V → ℝ × ℝ) (arc : ∀ u v : V, G.Adj u v → C(unitInterval, ℝ × ℝ)),
    Function.Injective point ∧
    (∀ u v h, (arc u v h) 0 = point u ∧ (arc u v h) 1 = point v) ∧
    (∀ u v h, Function.Injective (arc u v h)) ∧
    (∀ u v h (t : unitInterval) w, 0 < (t : ℝ) → (t : ℝ) < 1 →
      (arc u v h) t ≠ point w) ∧
    (∀ u v h x y k (s t : unitInterval),
      0 < (s : ℝ) → (s : ℝ) < 1 → 0 < (t : ℝ) → (t : ℝ) < 1 →
      (arc u v h) s = (arc x y k) t →
      (u = x ∧ v = y) ∨ (u = y ∧ v = x))

/-- The sum of edge lengths along a finite graph walk. -/
def walkLength {V : Type} {G : SimpleGraph V} (length : V → V → ℝ)
    {u v : V} : G.Walk u v → ℝ
  | .nil => 0
  | @SimpleGraph.Walk.cons _ _ u w _ _ p => length u w + walkLength length p

/-- The infimum of lengths of actual walks between the two vertices. -/
noncomputable def graphDistance {V : Type} (G : SimpleGraph V)
    (length : V → V → ℝ) (u v : V) : ℝ :=
  sInf (Set.range (fun p : G.Walk u v => walkLength length p))

/-- One universal distortion bound for finite connected planar graphs with
arbitrary symmetric positive edge lengths, realized in a real `L¹` space. -/
def MainStatement : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (length : Fin n → Fin n → ℝ),
      G.Connected → IsPlanar G →
      (∀ u v, length u v = length v u) →
      (∀ u v, G.Adj u v → 0 < length u v) →
      ∃ (Ω : Type) (measurable : MeasurableSpace Ω)
          (μ : @MeasureTheory.Measure Ω measurable)
          (f : Fin n → @MeasureTheory.Lp Ω ℝ measurable _ 1 μ),
        ∀ x y, graphDistance G length x y ≤ ‖f x - f y‖ ∧
          ‖f x - f y‖ ≤ C * graphDistance G length x y

theorem planar_graph_metrics_embed_L1 : MainStatement := by
  sorry

end PlanarL1

end OAI
