import OAI.NumberTheory.Jacobsthal.Estimates.UnmarkedTransform

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open AbsorptionCutoff.Renewal

noncomputable def costTransform (μ : Measure ℝ) (eta : ℝ) : ℝ≥0∞ :=
  ∫⁻ G, ENNReal.ofReal (Real.exp (eta*G)) ∂μ

lemma costTransform_zero (μ : Measure ℝ) : costTransform μ 0 = μ univ := by simp [costTransform]

lemma costTransform_conv (μ ν : Measure ℝ) [SFinite ν] (eta : ℝ) :
    costTransform (μ ∗ ν) eta = costTransform μ eta*costTransform ν eta := by
  have hm : Measurable (fun G : ℝ => ENNReal.ofReal (Real.exp (eta*G))) := by fun_prop
  rw [costTransform,Measure.lintegral_conv hm]
  have hi (x : ℝ) : (∫⁻ y, ENNReal.ofReal (Real.exp (eta*(x+y))) ∂ν) =
      ENNReal.ofReal (Real.exp (eta*x))*costTransform ν eta := by
    simp_rw [mul_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  simp_rw [hi]
  exact lintegral_mul_const _ hm

lemma conv_mass (μ ν : Measure ℝ) [SFinite ν] : (μ ∗ ν) univ = μ univ*ν univ := by
  simpa only [costTransform_zero] using costTransform_conv μ ν 0

lemma convPow_costTransform (μ : Measure ℝ) [SFinite μ] (eta : ℝ) (n : ℕ) :
    costTransform (convPow μ n) eta = (costTransform μ eta)^n := by
  induction n with
  | zero => simp [convPow_zero,costTransform]
  | succ n ih => rw [convPow_succ,costTransform_conv,ih,pow_succ]

lemma renewal_costTransform (μ : Measure ℝ) [SFinite μ] (eta : ℝ) :
    costTransform (renewalMeasure μ) eta = (1-costTransform μ eta)⁻¹ := by
  rw [costTransform,renewalMeasure,lintegral_sum_measure]
  change (∑' n, costTransform (convPow μ n) eta) = _
  simp_rw [convPow_costTransform]
  exact ENNReal.tsum_geometric _

noncomputable def unmarkedPotential : Measure ℝ := renewalMeasure unmarkedCostLaw

lemma unmarkedPotential_mass : unmarkedPotential univ = markProbability⁻¹ := by
  have he := renewal_costTransform unmarkedCostLaw 0
  rw [costTransform_zero,costTransform_zero,unmarkedCostLaw_mass,
    ENNReal.sub_sub_cancel (by simp : (1:ℝ≥0∞) ≠ ∞) markProbability_lt_one.le] at he
  exact he

instance unmarkedPotential_isFiniteMeasure : IsFiniteMeasure unmarkedPotential := by
  constructor
  rw [unmarkedPotential_mass]
  exact lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr markProbability_pos.ne')

noncomputable def geometricMarkedCostLaw : Measure ℝ := markedCostLaw ∗ unmarkedPotential

instance geometricMarkedCostLaw_isProbabilityMeasure : IsProbabilityMeasure geometricMarkedCostLaw := by
  constructor
  rw [geometricMarkedCostLaw,conv_mass,markedCostLaw_mass,unmarkedPotential_mass]
  exact ENNReal.mul_inv_cancel markProbability_pos.ne' (lt_trans markProbability_lt_one (by simp)).ne

lemma geometricMarked_costTransform (eta : ℝ) :
    costTransform geometricMarkedCostLaw eta =
      costTransform markedCostLaw eta*(1-costTransform unmarkedCostLaw eta)⁻¹ := by
  rw [geometricMarkedCostLaw,costTransform_conv,unmarkedPotential,renewal_costTransform]

lemma geometricMarked_exponential_moment : ∃ eta : ℝ, 0 < eta ∧
    costTransform geometricMarkedCostLaw eta < ∞ := by
  obtain ⟨eta,heta,hU,hM⟩ := exists_subcritical_unmarked_transform
  refine ⟨eta,heta,?_⟩
  rw [geometricMarked_costTransform]
  have hsub : (1:ℝ≥0∞)-costTransform unmarkedCostLaw eta ≠ 0 :=
    (tsub_pos_iff_lt.mpr hU).ne'
  exact ENNReal.mul_lt_top hM (lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr hsub))

lemma conv_ae_lower {μ ν : Measure ℝ} [SFinite μ] [SFinite ν] {a b : ℝ}
    (hμ : ∀ᵐ x ∂μ, a ≤ x) (hν : ∀ᵐ y ∂ν, b ≤ y) :
    ∀ᵐ z ∂(μ ∗ ν), a+b ≤ z := by
  rw [Measure.conv]
  apply (ae_map_iff measurable_add.aemeasurable measurableSet_Ici).mpr
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le measurable_const measurable_add)).mpr
  filter_upwards [hμ] with x hx
  filter_upwards [hν] with y hy
  linarith

lemma convPow_ae_nonneg (μ : Measure ℝ) [SFinite μ] (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (n : ℕ) :
    ∀ᵐ x ∂convPow μ n, 0 ≤ x := by
  induction n with
  | zero => simp [convPow_zero]
  | succ n ih =>
    rw [convPow_succ]
    simpa only [zero_add] using conv_ae_lower ih hμ

lemma unmarkedPotential_ae_nonneg : ∀ᵐ G ∂unmarkedPotential, 0 ≤ G := by
  rw [unmarkedPotential,renewalMeasure,Measure.ae_sum_iff]
  intro n
  apply convPow_ae_nonneg
  filter_upwards [source_unmarked_cost_lower] with G hG
  exact positive_cost_of_lower hG

lemma geometricMarked_cost_lower : ∀ᵐ G ∂geometricMarkedCostLaw, Real.log (4/3) ≤ G := by
  rw [geometricMarkedCostLaw]
  simpa only [add_zero] using conv_ae_lower source_marked_cost_lower unmarkedPotential_ae_nonneg

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
