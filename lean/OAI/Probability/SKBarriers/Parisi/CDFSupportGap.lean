import Mathlib
import OAI.Probability.SKBarriers.Scalar.DyadicPenalty
import OAI.Probability.SKBarriers.Gaussian.LipschitzObservable
import OAI.Probability.SKBarriers.Scalar.ScalarPathMoment
import OAI.Probability.SKBarriers.Parisi.CDFZeroSupport

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem chain_coefficients_squares (β : ℝ) (l : List (ℝ × ℝ≥0)) :
    (∑ i : Fin l.length, (β*Real.sqrt ((l.get i).2:ℝ))^2)=β^2*(chainDuration l:ℝ) := by
  simp_rw [mul_pow,Real.sq_sqrt (l.get _).2.coe_nonneg]
  rw [← Finset.mul_sum]
  congr 1
  have H := chainDuration_ofFn l.length (fun i => l.get i)
  rw [List.ofFn_get] at H
  exact_mod_cast H.symm

theorem scalarMagnetization_square_lipschitz :
    LipschitzWith 2 (fun x => (scalarMagnetization x)^2) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,NNReal.coe_ofNat]
  exact (abs_sq_sub_sq_le_two (scalarMagnetization_abs_le_one x)
    (scalarMagnetization_abs_le_one y)).trans (mul_le_mul_of_nonneg_left
      (by simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using scalarMagnetization_lipschitz.dist_le_mul x y)
      (by norm_num))

theorem scalarCDFValue_duration_zero (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α) (s : ℝ) :
    scalarCDFValue β α s 0=scalarSpinTerminal := by
  funext x
  exact scalarCDFOperator_eq_chain scalarSpinTerminal_regular scalarSpinTerminal_lipschitz β hα hm
    [] (by simp) s 0 (by simp) rfl trivial x

theorem scalarCDFGradient_duration_zero (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α) (s : ℝ) :
    scalarCDFGradient β α s 0=scalarMagnetization := by
  funext x
  have H := scalarCDFValue_hasDerivAt β hα hm s 0 (by simp) x
  rw [scalarCDFValue_duration_zero β hα hm s] at H
  exact H.unique (scalarSpinTerminal_hasDerivAt x)

theorem scalarCDFOverlap_one_lt (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α) : scalarCDFOverlap β α 1<1 := by
  have hb (x : ℝ) : |(scalarMagnetization x)^2|≤(1:ℝ≥0) := by
    rw [abs_of_nonneg (sq_nonneg _)]; exact scalarMagnetization_sq_le_one x
  have HT := dyadicScalarAverage_tendsto_lipschitz β hα hm scalarSpinTerminal_regular
    scalarSpinTerminal_lipschitz scalarMagnetization_square_lipschitz hb 0 1 le_rfl 0
  have H : scalarCDFAverage β α 0 1 scalarSpinTerminal (fun z => (scalarMagnetization z)^2) 0 ≤
      1-1/(2*(Real.cosh (1+2*β^2+4*(β^2)^2))^2) := by
    apply le_of_tendsto HT
    apply Eventually.of_forall
    intro n
    apply scalarHierarchyAverage_square_gap _ _ _
      (fun i => dyadicIntervals_mass_bounds hα n 0 1 (List.get_mem _ i))
      (scalarTimeChain_mass_monotone _ (dyadicIntervals_pairwise hm n 0 1)) (sq_nonneg β)
    rw [chain_coefficients_squares,dyadicIntervals_duration,NNReal.coe_one,mul_one]
  unfold scalarCDFOverlap
  simp only [sub_self,Real.toNNReal_zero,Real.toNNReal_one,
    scalarCDFValue_duration_zero β hα hm,scalarCDFGradient_duration_zero β hα hm]
  exact H.trans_lt (sub_lt_self _ (by positivity))

theorem scalarCDFParisi_support_away_one {β : ℝ} (hβ : β≠0)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β) :
    ∃ q∈Ico (0:ℝ) 1, (μ : Measure ℝ).support ⊆ Icc 0 q := by
  have HS := Measure.support_subset_of_isClosed (μ:=(μ : Measure ℝ))
    isClosed_Icc (supported_probability_ae μ hμ)
  have HC : IsCompact (μ : Measure ℝ).support :=
    isCompact_Icc.of_isClosed_subset (μ : Measure ℝ).isClosed_support HS
  have H0 := scalarCDFParisi_zero_mem_support hβ μ hμ hmin
  obtain ⟨q,hq⟩ := HC.exists_isGreatest ⟨0,H0⟩
  have hbound := HS hq.1
  have hq1 : q<1 := by
    by_contra H
    have he : q=1 := le_antisymm hbound.2 (le_of_not_gt H)
    have HG := scalarCDFParisi_overlap_on_support hβ μ hμ hmin hq.1
    rw [he] at HG
    have HH := scalarCDFOverlap_one_lt β (fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩)
      (cdf (μ : Measure ℝ)).mono
    linarith
  exact ⟨q,⟨hbound.1,hq1⟩,fun x hx => ⟨(HS hx).1,hq.2 hx⟩⟩

end SK.Analytic

end
end

end OAI
