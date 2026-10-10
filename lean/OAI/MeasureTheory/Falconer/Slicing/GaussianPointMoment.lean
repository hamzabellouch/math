import OAI.MeasureTheory.Falconer.Slicing.GaussianPointBand

namespace OAI

/-! # Point-pair overlap under the Gaussian slicing parameters -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussianPointBand_pair_parameter_bound (A : Fin h → Space d) (x y : Space d)
    {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (Space h)) {z | x ∈ gaussianPointBand A z r ∧ y ∈ gaussianPointBand A z r} ≤
      if ∀ i, |inner ℝ (x-y) (A i)| ≤ 2*r then ENNReal.ofReal ((2*r)^h) else 0 := by
  split_ifs with hh
  · exact (measure_mono (fun _ hz => hz.1)).trans_eq (gaussianPointBand_parameter_measure A x hr)
  · have he : {z : Space h | x ∈ gaussianPointBand A z r ∧ y ∈ gaussianPointBand A z r} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hh (gaussianPointBand_pair_difference A z hz.1 hz.2)
    rw [he,measure_empty]

theorem gaussianPointBand_pair_average (x y : Space d) {r : ℝ} (hr : 0 ≤ r) :
    ((gaussianRows d h).prod (volume : Measure (Space h)))
      {p | x ∈ gaussianPointBand p.1 p.2 r ∧ y ∈ gaussianPointBand p.1 p.2 r} ≤
      ENNReal.ofReal ((2*r)^h)*gaussianRows d h {A | ∀ i, |inner ℝ (x-y) (A i)| ≤ 2*r} := by
  let D : Set (Fin h → Space d) := {A | ∀ i, |inner ℝ (x-y) (A i)| ≤ 2*r}
  have hD : MeasurableSet D := by
    simp only [D,ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const
  have hS : MeasurableSet {p : (Fin h → Space d) × Space h |
      x ∈ gaussianPointBand p.1 p.2 r ∧ y ∈ gaussianPointBand p.1 p.2 r} := by
    change MeasurableSet {p : (Fin h → Space d) × Space h |
      (∀ i, |inner ℝ x (p.1 i)-p.2 i| ≤ r) ∧ (∀ i, |inner ℝ y (p.1 i)-p.2 i| ≤ r)}
    simp only [ofPred_and,ofPred_forall]
    apply MeasurableSet.inter <;> apply MeasurableSet.iInter <;> intro i <;>
      exact measurableSet_le (by fun_prop) measurable_const
  rw [Measure.prod_apply hS]
  calc
    _ ≤ ∫⁻ A, D.indicator (fun _ => ENNReal.ofReal ((2*r)^h)) A ∂gaussianRows d h := by
      apply lintegral_mono
      intro A
      change (volume : Measure (Space h))
        {z | x ∈ gaussianPointBand A z r ∧ y ∈ gaussianPointBand A z r} ≤ _
      simpa only [D,indicator_apply,mem_ofPred_eq] using gaussianPointBand_pair_parameter_bound A x y hr
    _ = _ := lintegral_indicator_const hD _

theorem gaussian_point_band_second_moment (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 ≤ r) :
    (∫⁻ p : (Fin h → Space d) × Space h, (μ (gaussianPointBand p.1 p.2 r))^2
      ∂(gaussianRows d h).prod volume) ≤
      ∫⁻ z : Space d × Space d, ENNReal.ofReal ((2*r)^h)*
        gaussianRows d h {A | ∀ i, |inner ℝ (z.1-z.2) (A i)| ≤ 2*r} ∂μ.prod μ := by
  let S : Set (((Fin h → Space d) × Space h) × (Space d × Space d)) :=
    {p | p.2.1 ∈ gaussianPointBand p.1.1 p.1.2 r ∧ p.2.2 ∈ gaussianPointBand p.1.1 p.1.2 r}
  have hS : MeasurableSet S := by
    change MeasurableSet {p : ((Fin h → Space d) × Space h) × (Space d × Space d) |
      (∀ i, |inner ℝ p.2.1 (p.1.1 i)-p.1.2 i| ≤ r) ∧
      (∀ i, |inner ℝ p.2.2 (p.1.1 i)-p.1.2 i| ≤ r)}
    simp only [ofPred_and,ofPred_forall]
    apply MeasurableSet.inter <;> apply MeasurableSet.iInter <;> intro i <;>
      exact measurableSet_le (by fun_prop) measurable_const
  have hsection (p : (Fin h → Space d) × Space h) :
      Prod.mk p ⁻¹' S = (gaussianPointBand p.1 p.2 r) ×ˢ (gaussianPointBand p.1 p.2 r) := rfl
  calc
    _ = (((gaussianRows d h).prod volume).prod (μ.prod μ)) S := by
      rw [Measure.prod_apply hS]
      apply lintegral_congr
      intro p
      rw [hsection,Measure.prod_prod,pow_two]
    _ = ∫⁻ z : Space d × Space d, ((gaussianRows d h).prod volume)
        {p | z.1 ∈ gaussianPointBand p.1 p.2 r ∧ z.2 ∈ gaussianPointBand p.1 p.2 r} ∂μ.prod μ :=
      Measure.prod_apply_symm hS
    _ ≤ _ := lintegral_mono (fun z => gaussianPointBand_pair_average z.1 z.2 hr)

end Falconer

end OAI
