import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoreMassFamily

namespace OAI

/-! The actual global restriction to the arithmetic compact core is
compact from the energy space to L2. The finite bump inequality gives
norm domination by the already compact family of localizations. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators MatrixGroups
namespace CubicFirstMoment

private lemma indicatorOne_bound {K : Set CubicThetaQuotient} (q : CubicThetaQuotient) :
    ‖K.indicator (fun _ => (1:ℂ)) q‖≤1 := by
  by_cases h : q∈K <;> simp [h]

def cubicThetaGlobalRestriction {K : Set CubicThetaQuotient} (hK : MeasurableSet K) :
    CubicThetaGlobalL2 →L[ℂ] CubicThetaGlobalL2 :=
  cubicThetaGlobalMultiplier (stronglyMeasurable_const.indicator hK).aestronglyMeasurable
    indicatorOne_bound

lemma cubicThetaGlobalRestriction_ae {K : Set CubicThetaQuotient} (hK : MeasurableSet K)
    (u : CubicThetaGlobalL2) :
    (cubicThetaGlobalRestriction hK u : CubicThetaQuotient → ℂ)=ᵐ[cubicThetaQuotientMeasure]
      K.indicator (fun q => u q) := by
  filter_upwards [cubicThetaGlobalMultiplier_ae
    (stronglyMeasurable_const.indicator hK).aestronglyMeasurable indicatorOne_bound u] with q hq
  change cubicThetaGlobalRestriction hK u q=K.indicator (fun _ => (1:ℂ)) q*u q at hq
  rw [hq]
  by_cases h : q∈K <;> simp [h]

def cubicThetaCoreRestriction (S : Finset SL(2,Eisenstein)) (V : ℝ) :
    cubicThetaGlobalEnergySpace →L[ℂ] CubicThetaGlobalL2 :=
  (cubicThetaGlobalRestriction (cubicThetaQuotientCore_compact S V).measurableSet).comp
    cubicThetaGlobalInclusion

lemma cubicThetaCoreMass_integral (c : CubicThetaQuotient) (u : cubicThetaGlobalEnergySpace) :
    ‖cubicThetaCoreMass c u‖^2 =
      ∫ q, (cubicThetaCoreBump c q)^2*‖cubicThetaGlobalInclusion u q‖^2
        ∂cubicThetaQuotientMeasure := by
  rw [cubicTheta_l2_norm_sq_measure]
  apply integral_congr_ae
  filter_upwards [cubicThetaCoreMultiplier_ae c (cubicThetaGlobalInclusion u)] with q hq
  change ‖cubicThetaCoreMultiplier c (cubicThetaGlobalInclusion u) q‖^2=_
  rw [hq,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma cubicThetaCoreMass_density_integrable (c : CubicThetaQuotient)
    (u : cubicThetaGlobalEnergySpace) :
    Integrable (fun q => (cubicThetaCoreBump c q)^2*‖cubicThetaGlobalInclusion u q‖^2)
      cubicThetaQuotientMeasure := by
  have h := (Lp.memLp (cubicThetaCoreMass c u)).integrable_norm_pow (by norm_num)
  apply h.congr
  filter_upwards [cubicThetaCoreMultiplier_ae c (cubicThetaGlobalInclusion u)] with q hq
  change ‖cubicThetaCoreMultiplier c (cubicThetaGlobalInclusion u) q‖^2=_
  rw [hq,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma cubicThetaCoreRestriction_norm_sq_le (S : Finset SL(2,Eisenstein)) (V : ℝ)
    (A : Finset CubicThetaQuotient)
    (hA : ∀ q∈cubicThetaQuotientCore S V, 1≤∑ c∈A, (cubicThetaCoreBump c q)^2)
    (u : cubicThetaGlobalEnergySpace) :
    ‖cubicThetaCoreRestriction S V u‖^2≤∑ c∈A, ‖cubicThetaCoreMass c u‖^2 := by
  classical
  rw [cubicTheta_l2_norm_sq_measure]
  simp_rw [cubicThetaCoreMass_integral]
  rw [← integral_finsetSum A (fun c _ => cubicThetaCoreMass_density_integrable c u)]
  apply integral_mono_ae
    ((Lp.memLp (cubicThetaCoreRestriction S V u)).integrable_norm_pow (by norm_num))
    (integrable_finsetSum A (fun c _ => cubicThetaCoreMass_density_integrable c u))
  filter_upwards [cubicThetaGlobalRestriction_ae
    (cubicThetaQuotientCore_compact S V).measurableSet (cubicThetaGlobalInclusion u)] with q hq
  change ‖cubicThetaGlobalRestriction (cubicThetaQuotientCore_compact S V).measurableSet
    (cubicThetaGlobalInclusion u) q‖^2≤_
  rw [hq,← Finset.sum_mul]
  by_cases h : q∈cubicThetaQuotientCore S V
  · simp only [Set.indicator_of_mem h]
    exact le_mul_of_one_le_left (sq_nonneg _) (hA q h)
  · simp only [Set.indicator_of_notMem h,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
    exact mul_nonneg (Finset.sum_nonneg (fun c _ => sq_nonneg _)) (sq_nonneg _)

theorem cubicThetaCoreRestriction_compact (S : Finset SL(2,Eisenstein)) (V : ℝ) :
    IsCompactOperator (cubicThetaCoreRestriction S V) := by
  obtain ⟨A,hA⟩ := cubicThetaCoreBump_sum_sq S V
  apply cubicThetaCompact_of_norm_domination (cubicThetaCoreRestriction S V)
    (cubicThetaCoreMassFamily A) (cubicThetaCoreMassFamily_compact A)
  refine ⟨1,fun u => ?_⟩
  rw [one_mul]
  apply _root_.le_of_sq_le_sq _ (_root_.norm_nonneg _)
  rw [cubicThetaCoreMassFamily_norm_sq]
  rw [Finset.sum_coe_sort A (fun c => ‖cubicThetaCoreMass c u‖^2)]
  exact cubicThetaCoreRestriction_norm_sq_le S V A hA u

end CubicFirstMoment

end

end OAI
