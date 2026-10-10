import OAI.Probability.InvariantIsing.Fields.PhysicalFieldPopulationLimit

namespace OAI

/-! Different limiting field populations give a quantitative comparison
of the physical mean pressures. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace InvariantIsing

theorem physical_mean_field_population_comparison {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : ∀ j, 0 < N j)
    (μ : (j : ℕ) → Measure (Orthogonal (N j))) [∀ j, IsProbabilityMeasure (μ j)]
    [∀ j, (μ j).IsMulRightInvariant] (eig : (j : ℕ) → Fin (N j) → ℝ)
    (g h : (j : ℕ) → Fin (N j) → A) (γ δ b : A → ℝ)
    (hg : Tendsto (fun j a => (spinGroupSize (g j) a : ℝ)/N j) atTop (𝓝 γ))
    (hh : Tendsto (fun j a => (spinGroupSize (h j) a : ℝ)/N j) atTop (𝓝 δ))
    {D : ℝ} (hD : 0 ≤ D) (hb : ∀ a, |b a| ≤ D) :
    ∀ ε > 0, ∀ᶠ j in atTop,
      |(∫ U, rotatedPressure (eig j) (matrixRotation U⁻¹) (fun i => b (g j i)) ∂μ j)-
        ∫ U, rotatedPressure (eig j) (matrixRotation U⁻¹) (fun i => b (h j i)) ∂μ j| ≤
      2*D*(∑ a, |γ a-δ a|)+ε := by
  have he a := (((tendsto_pi_nhds.mp hg) a).sub ((tendsto_pi_nhds.mp hh) a)).abs
  have hs := (tendsto_finsetSum Finset.univ (fun a _ => he a)).const_mul (2*D)
  intro ε hε
  have hsmall := hs.eventually (Iio_mem_nhds (lt_add_of_pos_right _ hε))
  filter_upwards [hsmall] with j hj
  exact (physical_mean_field_counts_le (hN j) (μ j) (eig j) (g j) (h j) b hD hb).trans hj.le

end InvariantIsing

end

end OAI
