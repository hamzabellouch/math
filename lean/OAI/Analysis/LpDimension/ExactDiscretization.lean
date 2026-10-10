import OAI.Analysis.LpDimension.Discretization

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace SubpolynomialLp

/-- Exact finite discretization in `n.choose 2` coordinates, including empty
and singleton families. -/
theorem exact_discretization_all_lengths (p : ℝ) (hp : 1 ≤ p) (n : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (x : Fin n → Lp ℝ (ENNReal.ofReal p) μ) (hx : Function.Injective x) :
    ∃ y : Fin n → Fin (n.choose 2) → ℝ, ∀ i j,
      coordinateDistance p (y i) (y j) = ‖x i - x j‖ := by
  by_cases hn : 2 ≤ n
  · exact exact_discretization_ge_one p hp n hn μ x hx
  · refine ⟨fun _ _ => 0, ?_⟩
    intro i j
    have hij : i = j := Fin.ext (by have := i.isLt; have := j.isLt; omega)
    subst j
    have hp0 : 0 < p := by linarith
    simp [coordinateDistance, Real.zero_rpow hp0.ne',
      Real.zero_rpow (inv_ne_zero hp0.ne')]

end SubpolynomialLp

namespace SubpolynomialLpExact

open SubpolynomialLp

/-- Every finite subset of a real `Lp` space embeds injectively into
`n.choose 2` real coordinates with their finite `Lp` distance. -/
theorem exact_discretization_embedding (p : ℝ) (hp : 1 ≤ p) (n : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (x : Fin n → Lp ℝ (ENNReal.ofReal p) μ) (hx : Function.Injective x) :
    ∃ y : Fin n → Fin (n.choose 2) → ℝ, Function.Injective y ∧
      ∀ i j, coordinateDistance p (y i) (y j) = ‖x i - x j‖ := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  obtain ⟨y, hy⟩ := exact_discretization_all_lengths p hp n μ x hx
  refine ⟨y, ?_, hy⟩
  intro i j hij
  apply hx
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hp0 : 0 < p := by linarith
  have hzero : coordinateDistance p (y i) (y j) = 0 := by
    rw [hij]
    simp [coordinateDistance, Real.zero_rpow hp0.ne',
      Real.zero_rpow (inv_ne_zero hp0.ne')]
  exact (hy i j).symm.trans hzero

/-- The exact discretization is an injective embedding into the real `Lp`
space on `n.choose 2` points equipped with counting measure. -/
theorem exact_discretization_lp_embedding (p : ℝ) (hp : 1 ≤ p) (n : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (x : Fin n → Lp ℝ (ENNReal.ofReal p) μ) (hx : Function.Injective x) :
    ∃ y : Fin n → Lp ℝ (ENNReal.ofReal p)
        (Measure.count : Measure (Fin (n.choose 2))),
      Function.Injective y ∧ ∀ i j, ‖y i - y j‖ = ‖x i - x j‖ := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  obtain ⟨y, hinj, hy⟩ := exact_discretization_embedding p hp n μ x hx
  refine ⟨fun i => finiteToLp p (y i), (finiteToLp_injective p).comp hinj, ?_⟩
  intro i j
  rw [← finiteToLp_sub, finiteToLp_norm p (by linarith)]
  exact hy i j

end SubpolynomialLpExact

end

end OAI
