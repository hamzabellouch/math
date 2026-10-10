import OAI.NumberTheory.DukePrimeDegree.Dynamics.HopfMaximal

namespace OAI

/-!
# Mean bounds from eventual orbit excursions

A conull union of positive finite excursions has nonnegative mean by the
finite Hopf inequality. This avoids assuming integrability of an unbounded
information function before truncating it.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree

/-- Positive partial sums somewhere along almost every orbit force a
nonnegative integral. -/
theorem integral_nonneg_of_ae_positive_birkhoffSum
    {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}
    {T : Y → Y} {f : Y → ℝ} (hT : MeasurePreserving T μ μ)
    (hf : Integrable f μ) (hfm : Measurable f)
    (hexc : ∀ᵐ x ∂μ, ∃ n : ℕ, 0 < birkhoffSum T f n x) :
    0 ≤ ∫ x, f x ∂μ := by
  let E : ℕ → Set Y := fun n => {x | 0 < positiveRunningSum T f n x}
  have hEm (n : ℕ) : MeasurableSet (E n) :=
    measurableSet_lt measurable_const (measurable_positiveRunningSum hT.measurable hfm n)
  have hmono : Monotone E := by
    intro a b hab x hx
    exact hx.trans_le (positiveRunningSum_mono T f x hab)
  have hconull : ∀ᵐ x ∂μ, x ∈ ⋃ n, E n := by
    filter_upwards [hexc] with x hx
    obtain ⟨n, hn⟩ := hx
    exact mem_iUnion.mpr ⟨n, hn.trans_le (birkhoffSum_le_positiveRunningSum T f n x)⟩
  have hlim := tendsto_setIntegral_of_monotone hEm hmono hf.integrableOn
  have heq : (∫ x in ⋃ n, E n, f x ∂μ) = ∫ x, f x ∂μ := by
    rw [Measure.restrict_congr_set (show (⋃ n, E n) =ᵐ[μ] (univ : Set Y) from
      hconull.mono (fun x hx => by simp [hx]))]
    simp
  rw [heq] at hlim
  apply ge_of_tendsto hlim
  exact Eventually.of_forall fun n => finite_hopf_maximal hT hf hfm n

/-- A bounded observable whose orbit average is eventually below `c`
has mean at most `c`. -/
theorem integral_le_of_ae_birkhoffSum_lt
    {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [IsProbabilityMeasure μ]
    {T : Y → Y} {g : Y → ℝ} (hT : MeasurePreserving T μ μ)
    (hg : Integrable g μ) (hgm : Measurable g) (c : ℝ)
    (hexc : ∀ᵐ x ∂μ, ∃ n : ℕ, birkhoffSum T g n x < c * n) :
    (∫ x, g x ∂μ) ≤ c := by
  have h := integral_nonneg_of_ae_positive_birkhoffSum hT
    ((integrable_const c).sub hg) (measurable_const.sub hgm) ?_
  · change 0 ≤ ∫ x, c - g x ∂μ at h
    rw [integral_sub (integrable_const c) hg] at h
    simpa using (sub_nonneg.mp h)
  · filter_upwards [hexc] with x hx
    obtain ⟨n, hn⟩ := hx
    refine ⟨n, ?_⟩
    change 0 < ∑ k ∈ Finset.range n, (c - g (T^[k] x))
    rw [Finset.sum_sub_distrib]
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm,
      birkhoffSum]
      using sub_pos.mpr hn

end DukePrimeDegree

end

end OAI
