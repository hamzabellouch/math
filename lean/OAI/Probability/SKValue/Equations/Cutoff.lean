import Mathlib
import OAI.Probability.SKValue.Model

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue

end SKValue

namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

noncomputable def OrderParameter.cutoff (γ : OrderParameter) (t : ℝ) : ℝ :=
  (Ico (0 : ℝ) 1).indicator γ.coeff t

lemma OrderParameter.cutoff_measurable (γ : OrderParameter) : Measurable γ.cutoff := by
  apply measurable_of_restrict_of_restrict_compl (s := Ico (0 : ℝ) 1) measurableSet_Ico
  · have hm : Monotone (fun t : Ico (0 : ℝ) 1 ↦ γ.coeff t) :=
      fun x y hxy ↦ γ.monotone x.property y.property hxy
    change Measurable (fun t : Ico (0 : ℝ) 1 ↦ γ.cutoff t)
    convert hm.measurable using 1
    funext t
    exact Set.indicator_of_mem t.property γ.coeff
  · have he : ((Ico (0 : ℝ) 1)ᶜ).domRestrict γ.cutoff = fun _ ↦ (0 : ℝ) := by
      funext t
      exact Set.indicator_of_notMem t.property γ.coeff
    rw [he]
    exact measurable_const

lemma OrderParameter.cutoff_nonneg (γ : OrderParameter) (t : ℝ) : 0≤γ.cutoff t := by
  by_cases ht : t∈Ico (0 : ℝ) 1
  · simpa only [OrderParameter.cutoff, Set.indicator_of_mem ht] using γ.nonneg t ht
  · simp only [OrderParameter.cutoff, Set.indicator_of_notMem ht, le_refl]

lemma OrderParameter.cutoff_integrable (γ : OrderParameter) : Integrable γ.cutoff := by
  apply (integrable_indicator_iff measurableSet_Ico).mpr
  have hi : IntegrableOn γ.coeff (Icc (0 : ℝ) 1) :=
    (integrableOn_Icc_iff_integrableOn_Ioc (by finiteness)).mpr γ.integrable
  exact hi.mono_set Ico_subset_Icc_self

noncomputable def limitedControl {Ω : Type*} (α : ℝ≥0 → Ω → ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  α (min (Real.toNNReal s) 1) ω

lemma Admissible.limited_measurable {W : BrownianSpace} {t : ℝ}
    {α : ℝ≥0 → W.Ω → ℝ} (hα : Admissible W t α) :
    Measurable (fun p : ℝ×W.Ω ↦ limitedControl α p.1 p.2) := by
  have hj : Measurable (fun p : Iic (1 : ℝ≥0) × W.Ω ↦ α p.1 p.2) := by
    apply (hα.1 1).comp
    exact measurable_fst.prodMk (measurable_snd.mono le_rfl ((shiftedFiltration W t).le 1))
  exact hj.comp (((measurable_real_toNNReal.comp measurable_fst).min measurable_const).subtype_mk (h := fun p ↦ Set.mem_Iic.mpr (min_le_right _ _) ) |>.prodMk measurable_snd)

lemma limitedControl_eq {W : BrownianSpace} (α : ℝ≥0 → W.Ω → ℝ) {s : ℝ}
    (hs : s≤1) (ω : W.Ω) : limitedControl α s ω=α (Real.toNNReal s) ω := by
  have hs' : Real.toNNReal s≤(1 : ℝ≥0) := Real.toNNReal_le_iff_le_coe.mpr hs
  simp only [limitedControl, min_eq_left hs']

lemma Admissible.limited_bound {W : BrownianSpace} {t : ℝ} {α : ℝ≥0 → W.Ω → ℝ}
    (hα : Admissible W t α) (s : ℝ) (ω : W.Ω) : |limitedControl α s ω|≤1 := hα.2 _ _

lemma OrderParameter.intervalIntegrable (γ : OrderParameter) :
    IntervalIntegrable γ.coeff volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr γ.integrable

lemma OrderParameter.shift_integrable (γ : OrderParameter) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun s ↦ γ.coeff (t+s)) volume 0 (1-t) := by
  have hi := γ.intervalIntegrable.mono_set (show uIcc t 1⊆uIcc (0 : ℝ) 1 by
    rw [uIcc_of_le ht.2, uIcc_of_le (by norm_num : (0 : ℝ)≤1)]
    exact Icc_subset_Icc ht.1 le_rfl)
  simpa only [sub_self] using hi.comp_add_left t

end SKValue

end

end OAI
