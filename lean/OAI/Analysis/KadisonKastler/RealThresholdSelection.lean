import OAI.Analysis.KadisonKastler.GoodProjectionCut
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! # Selecting a spectral threshold in the unit interval

The finite spectral cut functions vanish outside [-1,1]. Their global
energy estimates therefore apply to a finite measure of total mass two.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

theorem exists_good_real_threshold (f g : ℝ → ℝ)
    (hf : Integrable f) (hg : Integrable g)
    (hfs : ∀ t, t ∉ Set.Icc (-1 : ℝ) 1 → f t = 0)
    (hgs : ∀ t, t ∉ Set.Icc (-1 : ℝ) 1 → g t = 0)
    (hf₀ : ∀ t, 0 ≤ f t) (hg₁ : ∀ t, g t ≤ 1)
    (A B δ c : ℝ) (hδ : 0 < δ) (hc : 0 < c)
    (hA : (∫ t, f t) ≤ A) (hB : B ≤ ∫ t, g t)
    (hsmall : A < δ * (B - 2 * c)) :
    ∃ t ∈ Set.Icc (-1 : ℝ) 1, f t ≤ δ ∧ c ≤ g t := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (-1 : ℝ) 1)
  let : IsFiniteMeasure μ := ⟨by
    change volume.restrict (Set.Icc (-1 : ℝ) 1) Set.univ < ⊤
    rw [Measure.restrict_apply_univ,Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  have hmass : μ.real Set.univ = 2 := by
    change (volume.restrict (Set.Icc (-1 : ℝ) 1)).real Set.univ = 2
    rw [measureReal_restrict_apply_univ,measureReal_def,Real.volume_Icc]
    norm_num
  have hfi : (∫ t, f t ∂μ) = ∫ t, f t :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hfs
  have hgi : (∫ t, g t ∂μ) = ∫ t, g t :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hgs
  have hmean : (∫ t, f t ∂μ) < δ * ((∫ t, g t ∂μ) - c * μ.real Set.univ) := by
    rw [hfi,hgi,hmass]
    nlinarith
  obtain ⟨t,htf,htg⟩ := exists_good_projection_cut_of_finite_measure (μ := μ) f g
    hf.integrableOn hg.integrableOn hf₀ hg₁ δ c hδ hc hmean
  refine ⟨t,?_,htf,htg⟩
  by_contra ht
  rw [hgs t ht] at htg
  exact (not_le_of_gt hc) htg

end

end KadisonKastler

end OAI
