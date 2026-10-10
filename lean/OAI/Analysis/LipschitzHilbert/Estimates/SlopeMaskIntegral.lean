import OAI.Analysis.LipschitzHilbert.Estimates.SlopeBoxMask
import OAI.Analysis.LipschitzHilbert.Estimates.MaskIntegral

namespace OAI

/-! The actual sinc-masked slope-box synthesis on a finite testing
measure. The amplitude bound is required only almost everywhere on that
measure, allowing restriction to the good testing set. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LipschitzHilbert

theorem exists_slope_mask_integral (C H A1 D : ℝ) (hC : 0 ≤ C) (hH : 0 ≤ H) (hD : 0 < D) :
    ∃ A L0 : ℝ, 2 < A ∧ 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
        (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ], μ univ ≠ 0 →
      ∀ (T : ι → SlopeBox) (F : ι → ℝ × ℝ → EuclideanSpace ℂ κ),
      (∀ i, Measurable (F i)) →
      (∀ᵐ z ∂μ, ∀ i, ‖F i z‖ ≤ L^C*((T i).weight (L^A1) D z)^8) →
      ∀ K : ℝ, 0 < K →
      (∀ s : ℝ, 0 < s → μ {z | s < ∑ i, (T i).weight (L^A1) D z} ≤
        ENNReal.ofReal (K^2/s^2)) →
      Integrable (fun z => ‖(∑ i, F i z)-(∑ i, (T i).mask L A z • F i z)‖) μ ∧
        (∫ z, ‖(∑ i, F i z)-(∑ i, (T i).mask L A z • F i z)‖ ∂μ) ≤
          2*L^(-H)*K*Real.sqrt ((μ univ).toReal) := by
  obtain ⟨A,L0,hA,hL0,hmask⟩ := exists_mask_parameters C H A1 D hC hH hD
  refine ⟨A,L0,hA,hL0,?_⟩
  intro L hL ι κ _ _ μ _ hμ T F hFmeas hF K hK hweak
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith : 0 < L0) hL
  apply mask_error_integral μ hμ F (fun i => (T i).mask L A)
    (fun i => (T i).weight (L^A1) D) hFmeas
    (fun i => ((T i).mask_continuous L A).measurable)
    (fun i => ((T i).weight_continuous _ D (Real.rpow_pos_of_pos hLpos _)).measurable)
    (L^C) (L^(-H)) K (by positivity) (by positivity) hK
    (fun i z => ((T i).weight_pos (Real.rpow_pos_of_pos hLpos _) D z).le) hF
  · intro i z
    exact hmask L hL ((T i).horizontal z) ((T i).transverse z)
  · exact hweak

theorem exists_slope_mask_integral_above (C H A1 D M : ℝ) (hC : 0 ≤ C) (hH : 0 ≤ H) (hD : 0 < D) :
    ∃ A L0 : ℝ, M < A ∧ 2 < A ∧ 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
        (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ], μ univ ≠ 0 →
      ∀ (T : ι → SlopeBox) (F : ι → ℝ × ℝ → EuclideanSpace ℂ κ),
      (∀ i, Measurable (F i)) →
      (∀ᵐ z ∂μ, ∀ i, ‖F i z‖ ≤ L^C*((T i).weight (L^A1) D z)^8) →
      ∀ K : ℝ, 0 < K →
      (∀ s : ℝ, 0 < s → μ {z | s < ∑ i, (T i).weight (L^A1) D z} ≤
        ENNReal.ofReal (K^2/s^2)) →
      Integrable (fun z => ‖(∑ i, F i z)-(∑ i, (T i).mask L A z • F i z)‖) μ ∧
        (∫ z, ‖(∑ i, F i z)-(∑ i, (T i).mask L A z • F i z)‖ ∂μ) ≤
          2*L^(-H)*K*Real.sqrt ((μ univ).toReal) := by
  obtain ⟨A,L0,hM,hA,hL0,hmask⟩ := exists_mask_parameters_above C H A1 D M hC hH hD
  refine ⟨A,L0,hM,hA,hL0,?_⟩
  intro L hL ι κ _ _ μ _ hμ T F hFmeas hF K hK hweak
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith : 0 < L0) hL
  apply mask_error_integral μ hμ F (fun i => (T i).mask L A)
    (fun i => (T i).weight (L^A1) D) hFmeas
    (fun i => ((T i).mask_continuous L A).measurable)
    (fun i => ((T i).weight_continuous _ D (Real.rpow_pos_of_pos hLpos _)).measurable)
    (L^C) (L^(-H)) K (by positivity) (by positivity) hK
    (fun i z => ((T i).weight_pos (Real.rpow_pos_of_pos hLpos _) D z).le) hF
  · intro i z
    exact hmask L hL ((T i).horizontal z) ((T i).transverse z)
  · exact hweak

end LipschitzHilbert

end

end OAI
