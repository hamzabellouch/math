import OAI.NumberTheory.DukePrimeDegree.Dynamics.HopfMaximal

namespace OAI

/-!
# Uniform discrete orbit averages

The finite Hopf inequality bounds the union over all averaging lengths.
The resulting measurable good set controls every positive integer time,
as needed before passing to the continuous diagonal flow.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace DukePrimeDegree

theorem positiveRunningSum_measure_bound
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    {g : Y → ℝ} (hg : Integrable g μ) (hgmeas : Measurable g)
    (hgnonneg : ∀ x, 0 ≤ g x) (c : ℝ) (hc : 0 < c) :
    μ (⋃ n : ℕ, {x | 0 < positiveRunningSum T (fun y => g y - c) n x}) ≤
      ENNReal.ofReal ((∫ x, g x ∂μ) / c) := by
  let f : Y → ℝ := fun x => g x - c
  let E : ℕ → Set Y := fun n => {x | 0 < positiveRunningSum T f n x}
  have hf : Integrable f μ := hg.sub (integrable_const c)
  have hfmeas : Measurable f := hgmeas.sub measurable_const
  have hEmeas (n : ℕ) : MeasurableSet (E n) :=
    measurableSet_lt measurable_const (measurable_positiveRunningSum hT.measurable hfmeas n)
  have hEmono : Monotone E := by
    intro a b hab x hx
    exact hx.trans_le (positiveRunningSum_mono T f x hab)
  have hbound (n : ℕ) : μ (E n) ≤ ENNReal.ofReal ((∫ x, g x ∂μ) / c) := by
    have hhopf := finite_hopf_maximal hT hf hfmeas n
    change 0 ≤ ∫ x in E n, g x - c ∂μ at hhopf
    rw [integral_sub hg.restrict (integrable_const c), setIntegral_const, smul_eq_mul] at hhopf
    have hsub : ∫ x in E n, g x ∂μ ≤ ∫ x, g x ∂μ :=
      setIntegral_le_integral hg (Eventually.of_forall hgnonneg)
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _)
      (div_nonneg (integral_nonneg hgnonneg) hc.le)).mpr
    apply (le_div_iff₀ hc).mpr
    change μ.real (E n) * c ≤ _
    linarith
  rw [hEmono.measure_iUnion]
  exact iSup_le hbound

/-- The complement of one measurable exceptional set controls all finite
averages, with the sharp Hopf bound on its measure. -/
theorem exists_discrete_average_good_set
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    {g : Y → ℝ} (hg : Integrable g μ) (hgmeas : Measurable g)
    (hgnonneg : ∀ x, 0 ≤ g x) (c : ℝ) (hc : 0 < c) :
    ∃ G : Set Y, MeasurableSet G ∧
      μ Gᶜ ≤ ENNReal.ofReal ((∫ x, g x ∂μ) / c) ∧
      ∀ x ∈ G, ∀ n : ℕ, birkhoffSum T g n x ≤ c * n := by
  let f : Y → ℝ := fun x => g x - c
  let B := ⋃ n : ℕ, {x | 0 < positiveRunningSum T f n x}
  have hfmeas : Measurable f := hgmeas.sub measurable_const
  have hB : MeasurableSet B := MeasurableSet.iUnion fun n =>
    measurableSet_lt measurable_const (measurable_positiveRunningSum hT.measurable hfmeas n)
  refine ⟨Bᶜ, hB.compl, ?_, ?_⟩
  · simpa only [compl_compl] using positiveRunningSum_measure_bound μ hT hg hgmeas hgnonneg c hc
  · intro x hx n
    have hnot : ¬ 0 < positiveRunningSum T f n x := by
      intro h
      exact hx (mem_iUnion.mpr ⟨n, h⟩)
    have hs := (birkhoffSum_le_positiveRunningSum T f n x).trans (le_of_not_gt hnot)
    have heq : birkhoffSum T f n x = birkhoffSum T g n x - (n : ℝ) * c := by
      change (∑ k ∈ Finset.range n, (g (T^[k] x) - c)) = _
      rw [Finset.sum_sub_distrib]
      simp [birkhoffSum]
    rw [heq] at hs
    linarith

end DukePrimeDegree

end

end OAI
