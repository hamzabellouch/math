import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspCoreEnergy

namespace OAI

/-! Mass above height two is bounded by the full energy above height one
and a mass error in the compact transition core. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCusp_high_mass (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests) :
    (∫ q in cubicThetaCuspNeighborhood δ 2, cubicThetaSectionNorm F q^2
      ∂cubicThetaQuotientMeasure)≤
    ∫ y in cubicThetaHorizontalCell ×ˢ Ioi (0:ℝ),
      ‖cubicThetaCuspCutoffSection δ F y.1 y.2‖^2/y.2^3 := by
  have hf : StronglyMeasurable (fun q => cubicThetaSectionNorm F q^2) :=
    ((cubicThetaSectionNorm_continuous F).pow 2).stronglyMeasurable
  rw [← cubicThetaCuspPullback_integral δ (fun q => cubicThetaSectionNorm F q^2)
    hf (by norm_num : (1:ℝ)≤2)]
  calc
    _ = ∫ y in cubicThetaHorizontalCell ×ˢ Ioi (2:ℝ),
        ‖cubicThetaCuspCutoffSection δ F y.1 y.2‖^2/y.2^3 := by
      apply setIntegral_congr_fun (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)
      rintro ⟨z,v⟩ hy
      dsimp only at hy ⊢
      have hv : 0<v := lt_trans (by norm_num : (0:ℝ)<2) hy.2
      rw [cubicThetaCuspPullback_mass δ F z hv,cubicThetaCuspCutoffSection,
        cubicThetaCuspCutoff_one hy.2.le,one_mul]
    _ ≤ _ := by
      apply setIntegral_mono_set (cubicThetaCuspCutoff_mass_integrable δ F)
      · filter_upwards [ae_restrict_mem (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)] with y hy
        exact div_nonneg (sq_nonneg _) (pow_nonneg hy.2.le 3)
      · exact Filter.Eventually.of_forall (fun y hy => ⟨hy.1,lt_trans (by norm_num : (0:ℝ)<2) hy.2⟩)

theorem cubicThetaCusp_exterior_mass {ε : ℝ} (hε : 0<ε) :
    ∃ (S : Finset SL(2,Eisenstein)) (B : ℝ), 0≤B ∧
      ∀ (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests),
    (∫ q in cubicThetaCuspNeighborhood δ 2, cubicThetaSectionNorm F q^2
      ∂cubicThetaQuotientMeasure)≤
    (1+ε)*(∫ q in cubicThetaCuspNeighborhood δ 1, cubicThetaQuotientEnergy F q
      ∂cubicThetaQuotientMeasure)+
    B*(∫ q in cubicThetaQuotientCore S 2, cubicThetaSectionNorm F q^2
      ∂cubicThetaQuotientMeasure) := by
  obtain ⟨S,hS⟩ := cubicThetaCuspTransition_core
  obtain ⟨B,hB,h⟩ := cubicThetaCusp_core_energy hε
  refine ⟨S,B,hB,fun δ F => ?_⟩
  exact (cubicThetaCusp_high_mass δ F).trans ((cubicThetaCusp_integrated_hardy δ F).trans
    (h _ (cubicThetaQuotientCore_compact S 2).measurableSet hS δ F))

end CubicFirstMoment

end

end OAI
