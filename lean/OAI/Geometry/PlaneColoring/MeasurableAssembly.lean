import Mathlib

namespace OAI

noncomputable section

namespace Problem160

/-- A countable cover admits a measurable least-index choice, so separated
small cells give a measurable proper coloring, not merely an arbitrary one. -/
theorem exists_measurable_unit_distance_coloring_of_center_cover
    {X I : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [Countable I] [Nonempty I] {k : ℕ}
    (center : I → X) (color : I → Fin k) (r : ℝ)
    (hcover : ∀ x : X, ∃ i : I, dist x (center i) ≤ r)
    (hdiam : 2 * r < 1)
    (hsep : ∀ i j : I, i ≠ j → color i = color j →
      1 + 2 * r < dist (center i) (center j)) :
    ∃ c : X → Fin k, Measurable c ∧
      ∀ x y : X, dist x y = 1 → c x ≠ c y := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat I
  have hcoverNat : ∀ x : X, ∃ n : ℕ, dist x (center (e n)) ≤ r := by
    intro x
    obtain ⟨i, hi⟩ := hcover x
    obtain ⟨n, rfl⟩ := he i
    exact ⟨n, hi⟩
  let pick : X → ℕ := fun x => Nat.find (hcoverNat x)
  have hpick : Measurable pick := by
    apply measurable_find hcoverNat
    intro n
    exact (isClosed_le (continuous_id.dist continuous_const) continuous_const).measurableSet
  let cell : X → I := fun x => e (pick x)
  have hcell (x : X) : dist x (center (cell x)) ≤ r := Nat.find_spec (hcoverNat x)
  refine ⟨fun x => color (cell x), ?_, ?_⟩
  · exact (measurable_of_countable (fun n => color (e n))).comp hpick
  · intro x y hdist hcolor
    by_cases hsame : cell x = cell y
    · have htriangle := dist_triangle x (center (cell x)) y
      have hx := hcell x
      have hy := hcell y
      rw [← hsame] at hy
      rw [dist_comm (center (cell x)) y] at htriangle
      linarith
    · have hfar := hsep (cell x) (cell y) hsame hcolor
      have htriangle₁ := dist_triangle (center (cell x)) x (center (cell y))
      have htriangle₂ := dist_triangle x y (center (cell y))
      have hx := hcell x
      have hy := hcell y
      rw [dist_comm (center (cell x)) x] at htriangle₁
      linarith

end Problem160

end

end OAI
