import OAI.MeasureTheory.Falconer.Recursion.PointRieszPotential

namespace OAI

/-! # A positive compact restriction with bounded measurable potential -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem positive_compact_bounded_function (μ : ProbabilityMeasure (Space d))
    (F : Space d → ℝ≥0∞) (hF : Measurable F) (hfinite : ∀ᵐ x ∂(μ : Measure (Space d)), F x < ∞) :
    ∃ K : Set (Space d), IsCompact K ∧ 0 < (μ : Measure (Space d)) K ∧
      ∃ B : ℝ, 0 < B ∧ ∀ x ∈ K, F x ≤ ENNReal.ofReal B := by
  let S (n : ℕ) : Set (Space d) := {x | F x ≤ ENNReal.ofReal (n+1 : ℝ)}
  have hS (n : ℕ) : MeasurableSet (S n) := measurableSet_le hF measurable_const
  have hfull : (⋃ n, S n) =ᵐ[(μ : Measure (Space d))] univ := by
    filter_upwards [hfinite] with x hx
    apply propext
    simp only [mem_iUnion,mem_univ,iff_true]
    obtain ⟨n,hn⟩ := exists_nat_gt (F x).toReal
    refine ⟨n,?_⟩
    change F x ≤ ENNReal.ofReal (n+1 : ℝ)
    rw [← ENNReal.ofReal_toReal hx.ne]
    exact ENNReal.ofReal_le_ofReal (by linarith only [hn])
  have hmass : (μ : Measure (Space d)) (⋃ n, S n) ≠ 0 := by
    rw [measure_congr hfull,measure_univ]
    exact one_ne_zero
  obtain ⟨n,hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hmass
  obtain ⟨K,hKS,hK,hKm⟩ := (hS n).exists_lt_isCompact hn
  refine ⟨K,hK,hKm,(n:ℝ)+1,by positivity,?_⟩
  intro x hx
  exact hKS hx

@[fun_prop] theorem euclideanRieszPotential_measurable (μ : Measure (Space d)) [SFinite μ]
    (u : ℝ) : Measurable (euclideanRieszPotential μ u) := by
  apply Measurable.lintegral_prod_right
  exact (by fun_prop : Measurable (fun p : Space d × Space d => (edist p.1 p.2)^(-u)))

theorem integrated_pulled_potential (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {m : ℕ} (P : Space d →L[ℝ] Space m) (u : ℝ) :
    (∫⁻ x, euclideanRieszPotential (μ.map P) u (P x) ∂μ) =
      PlanarFalconer.rieszEnergyOn (μ.map P) u := by
  rw [← lintegral_map (euclideanRieszPotential_measurable (μ.map P) u) P.measurable,
    PlanarFalconer.rieszEnergyOn,lintegral_prod _ (by fun_prop)]
  rfl

end Falconer

end OAI
