import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspIntegratedHardy
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspScalarIntegrals
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspNeighborhoodCover

namespace OAI

/-! The cutoff error is supported in the genuine compact arithmetic core.
The coefficient of the full cusp gradient can be any number above one. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCusp_derivative_integral_high (δ : SL(2,Eisenstein))
    (F : cubicThetaSmoothTests) :
    (∫ y in cubicThetaHorizontalCell ×ˢ Ioi (0:ℝ),
      ‖deriv (cubicThetaCuspCutoffSection δ F y.1) y.2‖^2/y.2)=
    ∫ y in cubicThetaHorizontalCell ×ˢ Ioi (1:ℝ),
      ‖deriv (cubicThetaCuspCutoffSection δ F y.1) y.2‖^2/y.2 := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)
    (fun y hy => ⟨hy.1,lt_trans zero_lt_one hy.2⟩)
  intro y hy
  have hv : y.2≤1 := le_of_not_gt (fun h => hy.2 ⟨hy.1.1,h⟩)
  rw [cubicThetaCuspCutoffSection_deriv_zero δ F y.1 hv,norm_zero,
    zero_pow (by norm_num : (2:ℕ)≠0),zero_div]

lemma cubicThetaCusp_transition_bound {K : Set CubicThetaQuotient}
    (hK : ∀ (δ : SL(2,Eisenstein)) (p : CubicThetaPoint),
      1≤cubicThetaPointHeight p → cubicThetaPointHeight p≤2 →
        cubicThetaQuotientMap (δ • p)∈K)
    (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests) (z : ℂ)
    {v : ℝ} (hv : 0<v) :
    (Icc (1:ℝ) 2).indicator (fun t => ‖cubicThetaSectionFunction F
      (cubicThetaMobius (cubicThetaFullComplex δ) (z,t))‖^2) v≤
    cubicThetaCuspPullback δ (K.indicator (fun q => cubicThetaSectionNorm F q^2)) (z,v) := by
  classical
  have hp := cubicThetaCuspPullback_apply δ
    (K.indicator (fun q => cubicThetaSectionNorm F q^2)) (cubicThetaVerticalPoint z v hv)
  change cubicThetaCuspPullback δ (K.indicator (fun q => cubicThetaSectionNorm F q^2))
    (z,v)=_ at hp
  by_cases ht : v∈Icc (1:ℝ) 2
  · rw [indicator_of_mem ht,hp,
      indicator_of_mem (hK δ (cubicThetaVerticalPoint z v hv) ht.1 ht.2),
      cubicThetaCusp_raw_norm δ F z hv]
  · rw [indicator_of_notMem ht]
    exact indicator_nonneg (fun q hq => sq_nonneg _) _

lemma cubicThetaCusp_core_energy {ε : ℝ} (hε : 0<ε) :
    ∃ B≥0, ∀ (K : Set CubicThetaQuotient), MeasurableSet K →
      (∀ (δ : SL(2,Eisenstein)) (p : CubicThetaPoint),
        1≤cubicThetaPointHeight p → cubicThetaPointHeight p≤2 →
          cubicThetaQuotientMap (δ • p)∈K) →
      ∀ (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests),
    (∫ y in cubicThetaHorizontalCell ×ˢ Ioi (0:ℝ),
      ‖deriv (cubicThetaCuspCutoffSection δ F y.1) y.2‖^2/y.2)≤
      (1+ε)*(∫ q in cubicThetaCuspNeighborhood δ 1,
        cubicThetaQuotientEnergy F q ∂cubicThetaQuotientMeasure)+
      B*(∫ q in K, cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure) := by
  obtain ⟨B,hB,hpoint⟩ := cubicThetaCuspCutoff_energy hε
  refine ⟨B,hB,?_⟩
  intro K hKm hK δ F
  let m : CubicThetaQuotient → ℝ := K.indicator (fun q => cubicThetaSectionNorm F q^2)
  have hm : Integrable m cubicThetaQuotientMeasure := (cubicThetaMass_integrable F).indicator hKm
  have hms : StronglyMeasurable m :=
    ((cubicThetaSectionNorm_continuous F).pow 2).stronglyMeasurable.indicator hKm
  have he := cubicThetaCuspPullback_integrable δ (cubicThetaGradientEnergy_integrable F) (le_refl 1)
  have hc := cubicThetaCuspPullback_integrable δ hm (le_refl 1)
  have hbound : (∫ y in cubicThetaHorizontalCell ×ˢ Ioi (1:ℝ),
      ‖deriv (cubicThetaCuspCutoffSection δ F y.1) y.2‖^2/y.2)≤
      ∫ y in cubicThetaHorizontalCell ×ˢ Ioi (1:ℝ),
        (1+ε)*(cubicThetaCuspPullback δ (cubicThetaQuotientEnergy F) y/y.2^3)+
        B*(cubicThetaCuspPullback δ m y/y.2^3) := by
    apply setIntegral_mono_on (cubicThetaCuspCutoff_derivative_integrable_high δ F)
      ((he.const_mul (1+ε)).add (hc.const_mul B))
      (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)
    intro y hy
    have hv : 0<y.2 := lt_trans zero_lt_one hy.2
    have h := (hpoint δ F y.1 y.2 hv).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (cubicThetaCusp_transition_bound hK δ F y.1 hv) hB))
    rw [← cubicThetaCuspPullback_energy δ F y.1 hv] at h
    have hd := div_le_div_of_nonneg_right h (pow_nonneg hv.le 3)
    convert hd using 1
    · field_simp [hv.ne']
    · dsimp [m]
      ring
  rw [cubicThetaCusp_derivative_integral_high δ F]
  apply hbound.trans
  rw [integral_add (he.const_mul _) (hc.const_mul _),integral_const_mul,integral_const_mul,
    cubicThetaCuspPullback_integral δ _ (cubicThetaQuotientEnergy_continuous F).stronglyMeasurable (le_refl 1),
    cubicThetaCuspPullback_integral δ m hms (le_refl 1)]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ hB
  calc
    (∫ q in cubicThetaCuspNeighborhood δ 1, m q ∂cubicThetaQuotientMeasure)≤
        ∫ q, m q ∂cubicThetaQuotientMeasure :=
      setIntegral_le_integral hm (Filter.Eventually.of_forall (fun q => indicator_nonneg (fun _ _ => sq_nonneg _) q))
    _ = _ := integral_indicator hKm

end CubicFirstMoment

end

end OAI
