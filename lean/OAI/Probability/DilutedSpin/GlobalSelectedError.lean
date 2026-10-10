import OAI.Probability.DilutedSpin.FullSelectedError

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

/-- The literal unnormalised score error from pert:error, with the quenched
center under the entire same-law reservoir disorder. -/
noncomputable def fullSelectedError
    (ξ : Fin M → Measure Y) (μ : Measure X) (ν : Measure I) (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) : ℝ :=
  ∫ z, fullSelectedDeviation T Q m base sel fixed D E t z u
    (∫ w, fullSelectedRawScore T Q m base sel fixed D E t w u ∂fullRootLaw ξ μ ν r s)
      ∂fullRootLaw ξ μ ν r s

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ)

omit [Countable I] [MeasurableSingletonClass I] [∀ index, IsProbabilityMeasure (ξ index)]
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem fullSelectedError_nonneg (u : ℝ) :
    0 ≤ fullSelectedError ξ μ ν r s T Q m base sel fixed D E t u :=
  integral_nonneg (fun z => fullSelectedDeviation_nonneg T Q m base sel fixed D E t z u _)

theorem measurable_fullSelectedError
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (fullSelectedError ξ μ ν r s T Q m base sel fixed D E t) :=
  (measurable_fullSelectedDeviation T Q m base sel fixed D E t hb
    (measurable_fullSelectedRawScore T Q m base sel fixed D E t hb).stronglyMeasurable.integral_prod_left'.measurable).stronglyMeasurable.integral_prod_left'.measurable

/-- Conditional/root decomposition proved for the actual tilted score. -/
theorem fullSelectedError_split
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    {u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) :
    fullSelectedError ξ μ ν r s T Q m base sel fixed D E t u ≤
      (∫ z, fullSelectedThermal T Q m base sel fixed D E t z u ∂fullRootLaw ξ μ ν r s)+
        rootDeviation (fullRootLaw ξ μ ν r s) (fun z => fullSelectedRawScore T Q m base sel fixed D E t z u) := by
  let P := fullRootLaw ξ μ ν r s
  let center := ∫ w, fullSelectedRawScore T Q m base sel fixed D E t w u ∂P
  have hci : Integrable (fun z : FullRootState Y X I M => (z.2.2.1:ℝ)) P :=
    (fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)
  have hiD : Integrable (fun z => fullSelectedDeviation T Q m base sel fixed D E t z u center) P := by
    apply ((hci.const_mul 2).add (integrable_const |center|)).mono'
      ((measurable_fullSelectedDeviation T Q m base sel fixed D E t hb measurable_const).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      dsimp only [Function.comp_apply,id_eq,Pi.add_apply,Pi.sub_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (fullSelectedDeviation_nonneg T Q m base sel fixed D E t z u center)]
      exact fullSelectedDeviation_bound T Q m base sel fixed D E t hD hE ht hu z center)
  have hiT : Integrable (fun z => fullSelectedThermal T Q m base sel fixed D E t z u) P := by
    apply (hci.const_mul 4).mono'
      ((measurable_fullSelectedThermal T Q m base sel fixed D E t hb).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      dsimp only [Function.comp_apply,id_eq,Pi.add_apply,Pi.sub_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (fullSelectedThermal_nonneg T Q m base sel fixed D E t z u)]
      exact fullSelectedThermal_bound T Q m base sel fixed D E t hD hE ht hu z)
  have hiS : Integrable (fun z => fullSelectedRawScore T Q m base sel fixed D E t z u) P := by
    apply (hci.const_mul 2).mono'
      ((measurable_fullSelectedRawScore T Q m base sel fixed D E t hb).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      dsimp only [Function.comp_apply,id_eq,Pi.add_apply,Pi.sub_apply]
      rw [Real.norm_eq_abs]
      exact fullSelectedRawScore_bound T Q m base sel fixed D E t hD hE ht hu z)
  have hh := integral_mono hiD (hiT.add ((hiS.sub (integrable_const center)).abs))
    (fun z => fullSelectedDeviation_split T Q m base sel fixed D E t z u center)
  simp only [Pi.add_apply,Pi.sub_apply] at hh
  rw [integral_add (f := fun z => fullSelectedThermal T Q m base sel fixed D E t z u)
    (g := fun z => |fullSelectedRawScore T Q m base sel fixed D E t z u-center|) hiT ((hiS.sub (integrable_const center)).abs)] at hh
  exact hh

theorem fullSelectedError_bound
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    {u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) :
    fullSelectedError ξ μ ν r s T Q m base sel fixed D E t u ≤ 4*(s:ℝ) := by
  let P := fullRootLaw ξ μ ν r s
  let center := ∫ w, fullSelectedRawScore T Q m base sel fixed D E t w u ∂P
  have hci : Integrable (fun z : FullRootState Y X I M => (z.2.2.1:ℝ)) P :=
    (fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)
  have hiS : Integrable (fun z => fullSelectedRawScore T Q m base sel fixed D E t z u) P := by
    apply (hci.const_mul 2).mono'
      ((measurable_fullSelectedRawScore T Q m base sel fixed D E t hb).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      simpa only [Real.norm_eq_abs,Function.comp_apply,id_eq] using fullSelectedRawScore_bound T Q m base sel fixed D E t hD hE ht hu z)
  have hav : |center| ≤ 2*(s:ℝ) := by
    have hh := abs_integral_le_integral_abs.trans (integral_mono hiS.abs (hci.const_mul 2)
      (fun z => fullSelectedRawScore_bound T Q m base sel fixed D E t hD hE ht hu z))
    simpa only [P,integral_const_mul,fullRoot_count_mean] using hh
  have hiD : Integrable (fun z => fullSelectedDeviation T Q m base sel fixed D E t z u center) P := by
    apply ((hci.const_mul 2).add (integrable_const |center|)).mono'
      ((measurable_fullSelectedDeviation T Q m base sel fixed D E t hb measurable_const).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      dsimp only [Function.comp_apply,id_eq,Pi.add_apply,Pi.sub_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (fullSelectedDeviation_nonneg T Q m base sel fixed D E t z u center)]
      exact fullSelectedDeviation_bound T Q m base sel fixed D E t hD hE ht hu z center)
  have hh := integral_mono hiD ((hci.const_mul 2).add (integrable_const |center|))
    (fun z => fullSelectedDeviation_bound T Q m base sel fixed D E t hD hE ht hu z center)
  simp only [Pi.add_apply] at hh
  rw [integral_add (hci.const_mul 2) (integrable_const |center|), integral_const_mul] at hh
  simp only [P,fullRoot_count_mean,integral_const,probReal_univ,smul_eq_mul,one_mul] at hh
  change fullSelectedError ξ μ ν r s T Q m base sel fixed D E t u ≤ _
  change fullSelectedError ξ μ ν r s T Q m base sel fixed D E t u ≤ _ at hh
  linarith

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
