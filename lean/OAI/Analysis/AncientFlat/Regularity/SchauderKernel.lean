import OAI.Analysis.AncientFlat.Regularity.SchauderTime

namespace OAI
noncomputable section
open Set Filter MeasureTheory Real FourierTransform
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction SchwartzMap
namespace ParabolicSchauder
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
def potential (f : ℝ → (V →ᵇ ℂ)) (t : ℝ) (x : V) : ℂ :=
  ∫ s in Ioo 0 t, ∫ y : V, f s y * BiharmonicKernel.kernel (t-s) (x-y)
lemma potential_eq_smoothPotential (f : ℝ → (V →ᵇ ℂ)) (t : ℝ) :
    potential f t = smoothPotential FrozenParametrix.heatOne f t := by
  funext x
  unfold potential smoothPotential SourceFrozenRows.duhamel
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  unfold SourceFrozenRows.value ScaledSchwartzConvolution.value
  simp only [Real.one_rpow,mul_one,ContinuousLinearMap.lsmul_apply,smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with y
  rw [BiharmonicKernel.kernel_eq_scaled (t-s) (sub_pos.mpr hs.2),
    FrozenParametrix.quarter_root (t-s) (sub_pos.mpr hs.2),inv_pow]
  rfl

theorem fourth_derivative_holder (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ), 0 < h → h ≤ 1 →
      ∀ (f : ℝ → (V →ᵇ ℂ)) (F : ℝ), 0 ≤ F → Continuous f →
      (∀ s ∈ Icc 0 h, ∀ x y, ‖f s x-f s y‖ ≤ F*‖x-y‖^α) →
      (∀ t ∈ Icc 0 h, ContDiff ℝ 4 (potential f t)) ∧
      (∀ t ∈ Icc 0 h, ∀ x,
        ‖iteratedFDeriv ℝ 4 (potential f t) x‖ ≤ C*F*t^(α/4)) ∧
      (∀ t ∈ Icc 0 h, ∀ x y,
        ‖iteratedFDeriv ℝ 4 (potential f t) x-iteratedFDeriv ℝ 4 (potential f t) y‖ ≤
          C*F*‖x-y‖^α) ∧
      (∀ s ∈ Icc 0 h, ∀ t ∈ Icc 0 h, ∀ x,
        ‖iteratedFDeriv ℝ 4 (potential f t) x-iteratedFDeriv ℝ 4 (potential f s) x‖ ≤
          C*F*|t-s|^(α/4)) := by
  let K : SchwartzMap V ℂ := FrozenParametrix.heatOne
  obtain ⟨C,hC,hc⟩ := exists_fourth_bound K α hα hα1.le
  obtain ⟨D,hD,hd⟩ := exists_fourth_spatial_holder K α hα hα1
  obtain ⟨E,hE,he⟩ := exists_fourth_time_holder K α hα hα1
  refine ⟨C+D+E,by positivity,fun h _ _ f F hF hf hh => ?_⟩
  have hhold (t : ℝ) (ht : t ∈ Icc 0 h) :
      ∀ s ∈ Ioo 0 t, ∀ x y, ‖f s x-f s y‖≤F*‖x-y‖^α :=
    fun s hs => hh s ⟨hs.1.le,hs.2.le.trans ht.2⟩
  have hder (t : ℝ) (ht : t∈Icc 0 h) :
      iteratedFDeriv ℝ 4 (potential f t) = integratedJet K f t 4 := by
    rw [potential_eq_smoothPotential]
    exact derivative_smoothPotential K f hf α F t hα hα1.le hF ht.1 (hhold t ht)
  refine ⟨?_,?_,?_,?_⟩
  · intro t ht
    rw [potential_eq_smoothPotential]
    exact smoothPotential_contDiff K f hf α F t hα hα1.le hF ht.1 (hhold t ht)
  · intro t ht x
    rw [hder t ht]
    exact (hc f F t hF ht.1 (hhold t ht) x).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : C≤C+D+E) hF) (Real.rpow_nonneg ht.1 _))
  · intro t ht x y
    rw [hder t ht]
    exact (hd f hf F t hF ht.1 (hhold t ht) x y).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : D≤C+D+E) hF) (Real.rpow_nonneg (norm_nonneg _) _))
  · intro s hs t ht x
    rw [hder t ht,hder s hs]
    exact (he f hf F h hF hh s hs t ht x).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : E≤C+D+E) hF) (Real.rpow_nonneg (abs_nonneg _) _))
end ParabolicSchauder

end

end OAI
