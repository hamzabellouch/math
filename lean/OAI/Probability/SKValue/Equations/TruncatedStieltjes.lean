import Mathlib
import OAI.Probability.SKValue.Model

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma clamp_mem {T : ℝ} (hT : T∈Ico (0 : ℝ) 1) (t : ℝ) :
    min T (max 0 t)∈Ico (0 : ℝ) 1 :=
  ⟨le_min hT.1 (le_max_left _ _),(min_le_left _ _).trans_lt hT.2⟩

noncomputable def OrderParameter.truncatedStieltjes (γ : OrderParameter) (T : ℝ)
    (hT : T∈Ico (0 : ℝ) 1) : StieltjesFunction ℝ where
  toFun t := γ.coeff (min T (max 0 t))
  mono' a b hab := γ.monotone (clamp_mem hT a) (clamp_mem hT b)
    (min_le_min_left T (max_le_max_left 0 hab))
  right_continuous' t := by
    apply (γ.rightContinuous _ (clamp_mem hT t)).comp (f := fun s : ℝ ↦ min T (max 0 s))
      ((continuous_const.min (continuous_const.max continuous_id)).continuousWithinAt)
    intro u hu
    exact min_le_min_left T (max_le_max_left 0 hu)

lemma OrderParameter.truncatedStieltjes_zero (γ : OrderParameter) {T : ℝ}
    (hT : T∈Ico (0 : ℝ) 1) : γ.truncatedStieltjes T hT 0=γ.coeff 0 := by
  simp [OrderParameter.truncatedStieltjes,min_eq_right hT.1]

lemma OrderParameter.truncatedStieltjes_top (γ : OrderParameter) {T : ℝ}
    (hT : T∈Ico (0 : ℝ) 1) : γ.truncatedStieltjes T hT T=γ.coeff T := by
  simp [OrderParameter.truncatedStieltjes,max_eq_right hT.1]

noncomputable def OrderParameter.truncatedMass (γ : OrderParameter) (T : ℝ)
    (hT : T∈Ico (0 : ℝ) 1) : Measure ℝ :=
  (γ.truncatedStieltjes T hT).measure.restrict (Ioc 0 T)+
    ENNReal.ofReal (γ.coeff 0) • Measure.dirac 0

lemma OrderParameter.truncatedMass_univ (γ : OrderParameter) {T : ℝ}
    (hT : T∈Ico (0 : ℝ) 1) :
    γ.truncatedMass T hT univ=ENNReal.ofReal (γ.coeff T) := by
  have h0 := γ.nonneg 0 (by norm_num)
  have hm := γ.monotone (by norm_num : (0 : ℝ)∈Ico (0 : ℝ) 1) hT hT.1
  simp only [OrderParameter.truncatedMass,Measure.add_apply,Measure.restrict_apply_univ,
    Measure.smul_apply,Measure.dirac_apply_of_mem (mem_univ (0 : ℝ)),smul_eq_mul,mul_one,
    StieltjesFunction.measure_Ioc,γ.truncatedStieltjes_zero hT,γ.truncatedStieltjes_top hT]
  rw [←ENNReal.ofReal_add (sub_nonneg.mpr hm) h0]
  congr 1
  ring

instance OrderParameter.truncatedMass_finite (γ : OrderParameter) (T : ℝ)
    (hT : T∈Ico (0 : ℝ) 1) : IsFiniteMeasure (γ.truncatedMass T hT) :=
  ⟨by rw [γ.truncatedMass_univ hT]; exact ENNReal.ofReal_lt_top⟩

lemma OrderParameter.truncatedMass_cdf (γ : OrderParameter) {T t : ℝ}
    (hT : T∈Ico (0 : ℝ) 1) (ht : t∈Ico (0 : ℝ) 1) :
    γ.truncatedMass T hT (Iic t)=ENNReal.ofReal (min (γ.coeff t) (γ.coeff T)) := by
  have he : Iic t∩Ioc (0 : ℝ) T=Ioc 0 (min t T) := by
    ext s
    simp only [mem_inter_iff,mem_Iic,mem_Ioc,le_min_iff]
    tauto
  have hmin : min t T∈Ico (0 : ℝ) 1 := ⟨le_min ht.1 hT.1,(min_le_left _ _).trans_lt ht.2⟩
  have hm := γ.monotone (by norm_num : (0 : ℝ)∈Ico (0 : ℝ) 1) hmin hmin.1
  have h0 := γ.nonneg 0 (by norm_num)
  have hc : γ.truncatedStieltjes T hT (min t T)=min (γ.coeff t) (γ.coeff T) := by
    dsimp only [OrderParameter.truncatedStieltjes]
    rw [max_eq_right hmin.1,min_eq_right (min_le_right _ _)]
    rcases le_total t T with h | h
    · rw [min_eq_left h,min_eq_left (γ.monotone ht hT h)]
    · rw [min_eq_right h,min_eq_right (γ.monotone hT ht h)]
  have hm' : γ.coeff 0 ≤ min (γ.coeff t) (γ.coeff T) := by
    exact le_min (γ.monotone (by norm_num) ht ht.1) (γ.monotone (by norm_num) hT hT.1)
  simp only [OrderParameter.truncatedMass,Measure.add_apply,Measure.restrict_apply measurableSet_Iic,
    he,Measure.smul_apply,Measure.dirac_apply_of_mem (show (0 : ℝ)∈Iic t from ht.1),smul_eq_mul,mul_one,
    StieltjesFunction.measure_Ioc,γ.truncatedStieltjes_zero hT,hc]
  rw [←ENNReal.ofReal_add (sub_nonneg.mpr hm') h0]
  congr 1
  ring

lemma OrderParameter.truncatedMass_ae_mem (γ : OrderParameter) {T : ℝ}
    (hT : T∈Ico (0 : ℝ) 1) : ∀ᵐ s ∂γ.truncatedMass T hT,s∈Icc (0 : ℝ) T := by
  rw [ae_iff]
  change γ.truncatedMass T hT (Icc (0 : ℝ) T)ᶜ=0
  simp only [OrderParameter.truncatedMass,Measure.add_apply,
    Measure.restrict_apply measurableSet_Icc.compl,Measure.smul_apply]
  have he : (Icc (0 : ℝ) T)ᶜ∩Ioc 0 T=∅ := by
    exact disjoint_iff_inter_eq_empty.mp (disjoint_compl_left.mono_right Ioc_subset_Icc_self)
  rw [he,measure_empty,zero_add,Measure.dirac_apply]
  have hnot : (0 : ℝ)∉(Icc (0 : ℝ) T)ᶜ := notMem_compl_iff.mpr ⟨le_rfl,hT.1⟩
  rw [indicator_of_notMem hnot]
  simp

end SKValue

end

end OAI
