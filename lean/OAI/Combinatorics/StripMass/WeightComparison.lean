import Mathlib
import OAI.Combinatorics.StripMass.CoordinateBoxes

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory
lemma hasDerivAt_omegaLogHalf {x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasDerivAt omegaLogHalf
      ((1 - 2 * x - (Real.sqrt ((1 + x) / (2 * x)))⁻¹) / (4 * x * (1 - x))) x := by
  have hx0 : x ≠ 0 := hx.1.ne'
  have hd : (2 : ℝ) * x ≠ 0 := mul_ne_zero (by norm_num) hx0
  have hr : 1 < (1 + x) / (2 * x) := (lt_div_iff₀ (by linarith [hx.1])).2 (by linarith [hx.2])
  have ht : 1 < Real.sqrt ((1 + x) / (2 * x)) := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ (1 + x) / (2 * x)), Real.sqrt_nonneg ((1 + x) / (2 * x))]
  have hs : 0 < Real.sqrt (Real.sqrt ((1 + x) / (2 * x)) - 1) := Real.sqrt_pos.mpr (by linarith)
  have hs2 := Real.sq_sqrt (by linarith : 0 ≤ Real.sqrt ((1 + x) / (2 * x)) - 1)
  have ht2 := Real.sq_sqrt (by linarith : 0 ≤ (1 + x) / (2 * x))
  have ht2' : 2 * x * (Real.sqrt ((1 + x) / (2 * x))) ^ 2 = 1 + x := by
    rw [ht2]
    exact mul_div_cancel₀ (1 + x) hd
  have hdr : HasDerivAt (fun y : ℝ => (1 + y) / (2 * y)) (-1 / (2 * x ^ 2)) x := by
    apply (((hasDerivAt_id x).const_add 1).div ((hasDerivAt_id x).const_mul 2) hd).congr_deriv
    dsimp
    field_simp
    ring
  have hω := (((hdr.sqrt (by linarith : (1 + x) / (2 * x) ≠ 0)).sub_const 1).sqrt
    (by linarith : Real.sqrt ((1 + x) / (2 * x)) - 1 ≠ 0)).const_mul (1 / 2 : ℝ)
  have hdω : HasDerivAt omega
      (-1 / (16 * x ^ 2 * Real.sqrt ((1 + x) / (2 * x)) *
        Real.sqrt (Real.sqrt ((1 + x) / (2 * x)) - 1))) x := by
    apply hω.congr_deriv
    field_simp
    ring
  have hdlog := (hdω.log (omega_pos hx).ne').add
    (((hasDerivAt_id x).log hx0).const_mul (1 / 2 : ℝ))
  apply hdlog.congr_deriv
  dsimp only [omega, id_eq]
  have ht0 : Real.sqrt ((1 + x) / (2 * x)) ≠ 0 := by linarith
  have hs0 := hs.ne'
  have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
  generalize htdef : Real.sqrt ((1 + x) / (2 * x)) = t at *
  generalize hsdef : Real.sqrt (t - 1) = s at *
  field_simp
  ring_nf
  rw [hs2]
  nlinarith [ht2']

 

lemma omegaLogHalf_derivative_lower {x : ℝ} (hx : x ∈ Ioc 0 (1 / 2 : ℝ)) :
    -4 ≤ (1 - 2 * x - (Real.sqrt ((1 + x) / (2 * x)))⁻¹) / (4 * x * (1 - x)) := by
  have hr : 1 ≤ (1 + x) / (2 * x) := (le_div_iff₀ (by linarith [hx.1])).2 (by linarith [hx.2])
  have ht : 1 ≤ Real.sqrt ((1 + x) / (2 * x)) := Real.one_le_sqrt.mpr hr
  have hinv : (Real.sqrt ((1 + x) / (2 * x)))⁻¹ ≤ 1 := by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1) ht
  have hdp : 0 < 4 * x * (1 - x) := mul_pos (by linarith [hx.1]) (by linarith [hx.2])
  by_cases hsmall : x ≤ 1 / 8
  · have ht4 : (2 : ℝ) ^ 2 ≤ (1 + x) / (2 * x) :=
      (le_div_iff₀ (by linarith [hx.1])).2 (by nlinarith)
    have ht2 : 2 ≤ Real.sqrt ((1 + x) / (2 * x)) := by
      nlinarith [Real.sq_sqrt (by linarith : 0 ≤ (1 + x) / (2 * x)), Real.sqrt_nonneg ((1 + x) / (2 * x))]
    have hinv2 : (Real.sqrt ((1 + x) / (2 * x)))⁻¹ ≤ 1 / 2 := by
      simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 2) ht2
    have : 0 ≤ (1 - 2 * x - (Real.sqrt ((1 + x) / (2 * x)))⁻¹) / (4 * x * (1 - x)) :=
      div_nonneg (by linarith) hdp.le
    linarith
  · have hx8 : 1 / 8 ≤ x := le_of_not_ge hsmall
    have hden : 1 / 4 ≤ 4 * x * (1 - x) := by nlinarith [mul_nonneg hx.1.le (by linarith [hx.2] : 0 ≤ 1 / 2 - x)]
    apply (le_div_iff₀ hdp).2
    nlinarith [hx.2]

 
def upperLikelihoodWeight (β x : ℝ) : ℝ := omega x * x ^ (1 / 2 : ℝ) * Real.exp (β * x)

lemma upperLikelihoodWeight_exp {x : ℝ} (hx : x ∈ Ioo 0 1) (β : ℝ) :
    upperLikelihoodWeight β x = Real.exp (omegaLogHalf x + β * x) := by
  rw [omegaLogHalf, Real.exp_add, Real.exp_add, Real.exp_log (omega_pos hx)]
  simp only [upperLikelihoodWeight, Real.rpow_def_of_pos hx.1, mul_comm (Real.log x) (1 / 2 : ℝ)]

 

theorem upperLikelihoodWeight_monotone {β : ℝ} (hb : 4 ≤ β) :
    MonotoneOn (upperLikelihoodWeight β) (Ioo 0 (1 / 2 : ℝ)) := by
  have hh (x : ℝ) (hx : x ∈ Ioo 0 (1 / 2 : ℝ)) :
      HasDerivAt (fun x => omegaLogHalf x + β * x)
        ((1 - 2 * x - (Real.sqrt ((1 + x) / (2 * x)))⁻¹) / (4 * x * (1 - x)) + β) x := by
    apply ((hasDerivAt_omegaLogHalf ⟨hx.1, by linarith [hx.2]⟩).add ((hasDerivAt_id x).const_mul β)).congr_deriv
    simp only [mul_one]
  have hmono : MonotoneOn (fun x => omegaLogHalf x + β * x) (Ioo 0 (1 / 2 : ℝ)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo (0 : ℝ) (1 / 2 : ℝ))
      (fun x hx => (hh x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hh x (by simpa only [interior_Ioo] using hx)).hasDerivWithinAt)
    intro x hx
    have hx' : x ∈ Ioo 0 (1 / 2 : ℝ) := by simpa only [interior_Ioo] using hx
    linarith [omegaLogHalf_derivative_lower ⟨hx'.1, hx'.2.le⟩]
  intro x hx y hy hxy
  rw [upperLikelihoodWeight_exp ⟨hx.1, by linarith [hx.2]⟩,
    upperLikelihoodWeight_exp ⟨hy.1, by linarith [hy.2]⟩]
  exact Real.exp_le_exp.mpr (hmono hx hy hxy)

end

noncomputable section
open scoped BigOperators Pointwise
open Set MeasureTheory Filter

 
def scaledLaguerreWeight (a β x : ℝ) : ℝ := x ^ (a - 1) * Real.exp (-(β * x))

def scaledLaguerreDensity (N : ℕ) (a β : ℝ) : (Fin N → ℝ) → ℝ :=
  rawProductDensity N (fun _ => scaledLaguerreWeight a β)

 

def laguerreDensityScale (N : ℕ) (a β : ℝ) : ℝ :=
  (∏ _ : Fin N, β ^ (a - 1)) * ∏ i : Fin N, ∏ _j ∈ Finset.Ioi i, β

lemma laguerreDensityScale_pos (N : ℕ) (a : ℝ) {β : ℝ} (hb : 0 < β) :
    0 < laguerreDensityScale N a β := by
  unfold laguerreDensityScale
  exact mul_pos (Finset.prod_pos fun _ _ => Real.rpow_pos_of_pos hb _)
    (Finset.prod_pos fun _ _ => Finset.prod_pos fun _ _ => hb)

lemma pairKernel_smul {β : ℝ} (hb : β ≠ 0) (x y : ℝ) :
    pairKernel (β * x) (β * y) = β * pairKernel x y := by
  unfold pairKernel
  rw [← mul_sub, ← mul_add, mul_pow, pow_two β, mul_assoc,
    mul_div_mul_left _ _ hb, mul_div_assoc]

lemma laguerreDensity_scaled {N : ℕ} (a : ℝ) {β : ℝ} (hb : 0 < β)
    {y : Fin N → ℝ} (hy : ∀ i, 0 < y i) :
    laguerreDensity N a (β • y) = laguerreDensityScale N a β * scaledLaguerreDensity N a β y := by
  have hw (i : Fin N) : laguerreWeight a ((β • y) i) =
      β ^ (a - 1) * scaledLaguerreWeight a β (y i) := by
    simp only [Pi.smul_apply, smul_eq_mul, laguerreWeight, scaledLaguerreWeight,
      Real.mul_rpow hb.le (hy i).le, mul_assoc]
  have hp (i j : Fin N) : pairKernel ((β • y) i) ((β • y) j) =
      β * pairKernel (y i) (y j) := pairKernel_smul hb.ne' _ _
  simp only [laguerreDensity, hw, hp, Finset.prod_mul_distrib,
    laguerreDensityScale, scaledLaguerreDensity, rawProductDensity]
  ring

lemma orderedChamber_eq_laguerre_cutoff (N : ℕ) (R : ℝ) :
    orderedChamber N (Ioo 0 R) = laguerreDomain N ∩ cutoffEvent N R := by
  ext y
  constructor
  · exact fun h => ⟨⟨h.1, fun i => (h.2 i).1⟩, fun i => (h.2 i).2⟩
  · exact fun h => ⟨h.1.1, fun i => ⟨h.1.2 i, h.2 i⟩⟩

lemma measurableSet_orderedChamber_Ioo (N : ℕ) (R : ℝ) :
    MeasurableSet (orderedChamber N (Ioo 0 R)) := by
  rw [orderedChamber_eq_laguerre_cutoff]
  exact (isOpen_laguerreDomain N).measurableSet.inter (measurableSet_cutoffEvent N R)

lemma orderedChamber_smul {N : ℕ} (R : ℝ) {β : ℝ} (hb : 0 < β) :
    β • orderedChamber N (Ioo 0 R) = orderedChamber N (Ioo 0 (β * R)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨fun i j hij => mul_lt_mul_of_pos_left (hx.1 hij) hb,
      fun i => ⟨mul_pos hb (hx.2 i).1, mul_lt_mul_of_pos_left (hx.2 i).2 hb⟩⟩
  · intro hy
    refine ⟨β⁻¹ • y, ⟨?_, ?_⟩, smul_inv_smul₀ hb.ne' y⟩
    · exact fun i j hij => mul_lt_mul_of_pos_left (hy.1 hij) (inv_pos.mpr hb)
    · intro i
      constructor
      · exact mul_pos (inv_pos.mpr hb) (hy.2 i).1
      · change β⁻¹ * y i < R
        exact (inv_mul_lt_iff₀ hb).2 (hy.2 i).2

lemma integral_orderedChamber_scaled {N : ℕ} (R : ℝ) {β : ℝ} (hb : 0 < β)
    (f : (Fin N → ℝ) → ℝ) :
    (∫ y in orderedChamber N (Ioo 0 R), f (β • y)) =
      (β ^ N)⁻¹ * ∫ r in orderedChamber N (Ioo 0 (β * R)), f r := by
  simpa only [orderedChamber_smul R hb, Module.finrank_pi, Module.finrank_self,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, smul_eq_mul, mul_one,
    Nat.cast_id, nsmul_eq_mul, Nat.cast_one] using
    Measure.setIntegral_comp_smul_of_pos (volume : Measure (Fin N → ℝ)) f
      (orderedChamber N (Ioo 0 R)) hb

lemma inverseQuarterSum_smul {N : ℕ} {β : ℝ} (hb : 0 < β)
    {y : Fin N → ℝ} (hy : ∀ i, 0 < y i) :
    (∑ i, ((β • y) i)⁻¹) ^ (1 / 4 : ℝ) =
      (β ^ (1 / 4 : ℝ))⁻¹ * (∑ i, (y i)⁻¹) ^ (1 / 4 : ℝ) := by
  simp only [Pi.smul_apply, smul_eq_mul, mul_inv_rev, mul_comm (y _)⁻¹ β⁻¹,
    ← Finset.mul_sum]
  rw [Real.mul_rpow (inv_nonneg.mpr hb.le) (Finset.sum_nonneg fun i _ => (inv_pos.mpr (hy i)).le),
      Real.inv_rpow hb.le]

lemma measurable_scaledLaguerreWeight (a β : ℝ) : Measurable (scaledLaguerreWeight a β) := by
  unfold scaledLaguerreWeight
  fun_prop

lemma continuousOn_scaledLaguerreWeight (a β : ℝ) :
    ContinuousOn (scaledLaguerreWeight a β) (Ioi 0) := by
  unfold scaledLaguerreWeight
  exact (continuousOn_id.rpow_const (fun _ hx => Or.inl (ne_of_gt hx))).mul
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn)

lemma scaledLaguerreWeight_pos (a β : ℝ) {x : ℝ} (hx : 0 < x) :
    0 < scaledLaguerreWeight a β x := by
  exact mul_pos (Real.rpow_pos_of_pos hx _) (Real.exp_pos _)

lemma scaledLaguerreWeight_le (a : ℝ) {β x : ℝ} (hb : 1 ≤ β) (hx : 0 < x) :
    scaledLaguerreWeight a β x ≤ laguerreWeight a x := by
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos hx _).le
  apply Real.exp_le_exp.mpr
  nlinarith

lemma scaledLaguerreDensity_pos {N : ℕ} (a β : ℝ) {y : Fin N → ℝ}
    (hy : y ∈ laguerreDomain N) : 0 < scaledLaguerreDensity N a β y := by
  exact mul_pos (Finset.prod_pos fun i _ => scaledLaguerreWeight_pos a β (hy.2 i))
    (Finset.prod_pos fun i _ => Finset.prod_pos fun j hj =>
      pairKernel_pos (hy.2 i) (hy.1 (Finset.mem_Ioi.1 hj)))

lemma scaledLaguerreDensity_le {N : ℕ} (a : ℝ) {β : ℝ} (hb : 1 ≤ β)
    {y : Fin N → ℝ} (hy : y ∈ laguerreDomain N) :
    scaledLaguerreDensity N a β y ≤ laguerreDensity N a y := by
  apply mul_le_mul_of_nonneg_right _
    (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ =>
      pairKernel_nonneg (hy.2 i).le (hy.2 j).le)
  exact Finset.prod_le_prod₀ (fun i _ => (scaledLaguerreWeight_pos a β (hy.2 i)).le)
    (fun i _ => scaledLaguerreWeight_le a hb (hy.2 i))

lemma measurable_scaledLaguerreDensity (N : ℕ) (a β : ℝ) :
    Measurable (scaledLaguerreDensity N a β) := by
  unfold scaledLaguerreDensity rawProductDensity pairKernel
  apply Measurable.mul
  · exact Finset.measurable_prod _ fun i _ =>
      (measurable_scaledLaguerreWeight a β).comp (measurable_pi_apply i)
  · apply Finset.measurable_prod
    intro i _
    apply Finset.measurable_prod
    intro j _
    fun_prop

lemma integrableOn_scaledLaguerreDensity {N : ℕ} {a β : ℝ} (ha : 0 < a) (hb : 1 ≤ β) :
    IntegrableOn (scaledLaguerreDensity N a β) (laguerreDomain N) := by
  apply (integrableOn_laguerreDensity N ha).mono'
    (measurable_scaledLaguerreDensity N a β).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with y hy
  simpa only [Real.norm_eq_abs, abs_of_pos (scaledLaguerreDensity_pos a β hy)] using
    scaledLaguerreDensity_le a hb hy

abbrev inverseQuarterStatistic (N : ℕ) (y : Fin N → ℝ) : ℝ :=
  (∑ i, (y i)⁻¹) ^ (1 / 4 : ℝ)

lemma inverseQuarterStatistic_nonneg {N : ℕ} {y : Fin N → ℝ} (hy : ∀ i, 0 < y i) :
    0 ≤ inverseQuarterStatistic N y :=
  Real.rpow_nonneg (Finset.sum_nonneg fun i _ => (inv_pos.mpr (hy i)).le) _

lemma measurable_inverseQuarterStatistic (N : ℕ) : Measurable (inverseQuarterStatistic N) := by
  unfold inverseQuarterStatistic
  fun_prop

lemma integrableOn_scaledLaguerre_inverseQuarter {N : ℕ} {a β : ℝ}
    (ha : 1 / 4 < a) (hb : 1 ≤ β) :
    IntegrableOn (fun y => inverseQuarterStatistic N y * scaledLaguerreDensity N a β y)
      (laguerreDomain N) := by
  apply (integrableOn_laguerre_inverseQuarterSum ha).mono'
    ((measurable_inverseQuarterStatistic N).mul
      (measurable_scaledLaguerreDensity N a β)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with y hy
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inverseQuarterStatistic_nonneg hy.2)
    (scaledLaguerreDensity_pos a β hy).le)]
  exact mul_le_mul_of_nonneg_left (scaledLaguerreDensity_le a hb hy)
    (inverseQuarterStatistic_nonneg hy.2)

lemma scaledLaguerre_cutoffNormalizer_pos (N : ℕ) {a β R : ℝ}
    (ha : 0 < a) (hb : 1 ≤ β) (hR : 0 < R) :
    0 < ∫ y in orderedChamber N (Ioo 0 R), scaledLaguerreDensity N a β y := by
  rw [orderedChamber_eq_laguerre_cutoff]
  let S : Set (Fin N → ℝ) := laguerreDomain N ∩ cutoffEvent N R
  have hS : IsOpen S := (isOpen_laguerreDomain N).inter (isOpen_cutoffEvent N R)
  have hi : IntegrableOn (scaledLaguerreDensity N a β) S :=
    (integrableOn_scaledLaguerreDensity ha hb).mono_set inter_subset_left
  have hn : 0 ≤ᵐ[volume.restrict S] scaledLaguerreDensity N a β := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with r hr
    exact (scaledLaguerreDensity_pos a β hr.1).le
  apply (integral_pos_iff_support_of_nonneg_ae hn hi).2
  calc 0 < volume S := hS.measure_pos volume (laguerreDomain_cutoff_nonempty N hR)
       _ = (volume.restrict S) S := (Measure.restrict_apply_self _ _).symm
       _ ≤ (volume.restrict S) (Function.support (scaledLaguerreDensity N a β)) :=
          measure_mono fun _ hr => (scaledLaguerreDensity_pos a β hr.1).ne'

def upperLikelihood (N : ℕ) (β : ℝ) (y : Fin N → ℝ) : ℝ :=
  ∏ i, upperLikelihoodWeight β (y i)

lemma continuousOn_upperLikelihood (N : ℕ) (β : ℝ) :
    ContinuousOn (upperLikelihood N β) (coordinateBox (Fin N) (Ioi 0)) := by
  unfold upperLikelihood upperLikelihoodWeight
  apply continuousOn_finsetProd
  intro i _
  apply ContinuousOn.mul
  · exact (continuousOn_omega_Ioi.comp (continuous_apply i).continuousOn (show MapsTo (fun y : Fin N → ℝ => y i) (coordinateBox (Fin N) (Ioi 0)) (Ioi 0) from fun _ hy => hy i)).mul
      ((continuous_apply i).continuousOn.rpow_const (fun _ hy => Or.inl (hy i).ne'))
  · exact (Real.continuous_exp.comp (continuous_const.mul (continuous_apply i))).continuousOn

lemma upperLikelihood_pos (N : ℕ) (β : ℝ) {y : Fin N → ℝ}
    (hy : y ∈ coordinateBox (Fin N) (Ioo 0 1)) : 0 < upperLikelihood N β y := by
  apply Finset.prod_pos
  intro i _
  exact mul_pos (mul_pos (omega_pos (hy i)) (Real.rpow_pos_of_pos (hy i).1 _)) (Real.exp_pos _)

lemma upperLikelihood_monotone (N : ℕ) {β : ℝ} (hb : 4 ≤ β) :
    MonotoneOn (upperLikelihood N β) (coordinateBox (Fin N) (Ioo 0 (1 / 2 : ℝ))) := by
  intro x hx y hy hxy
  apply Finset.prod_le_prod₀
  · intro i _
    exact mul_nonneg (mul_nonneg (omega_nonneg _) (Real.rpow_nonneg (hx i).1.le _))
      (Real.exp_pos _).le
  · intro i _
    exact upperLikelihoodWeight_monotone hb (hx i) (hy i) (hxy i)

lemma scaledWeight_mul_upperLikelihoodWeight (β : ℝ) {x : ℝ} (hx : 0 < x) :
    scaledLaguerreWeight (1 / 2) β x * upperLikelihoodWeight β x = omega x := by
  unfold scaledLaguerreWeight upperLikelihoodWeight
  calc
    x ^ ((1 / 2 : ℝ) - 1) * Real.exp (-(β * x)) *
        (omega x * x ^ (1 / 2 : ℝ) * Real.exp (β * x)) =
      omega x * (x ^ ((1 / 2 : ℝ) - 1) * x ^ (1 / 2 : ℝ)) *
        (Real.exp (-(β * x)) * Real.exp (β * x)) := by ring
    _ = omega x := by
      rw [← Real.rpow_add hx, ← Real.exp_add]
      norm_num

lemma scaledDensity_mul_upperLikelihood {N : ℕ} (β : ℝ) {y : Fin N → ℝ}
    (hy : ∀ i, 0 < y i) :
    scaledLaguerreDensity N (1 / 2) β y * upperLikelihood N β y = density N y := by
  have hw : (∏ i, scaledLaguerreWeight (1 / 2) β (y i)) *
      (∏ i, upperLikelihoodWeight β (y i)) = ∏ i, omega (y i) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => scaledWeight_mul_upperLikelihoodWeight β (hy i)
  unfold scaledLaguerreDensity rawProductDensity upperLikelihood density
  rw [mul_right_comm, hw]

lemma orderedChamber_eq_positive_cutoff (N : ℕ) {R : ℝ} (hR : R ≤ 1) :
    orderedChamber N (Ioo 0 R) = orderedDomain N ∩ cutoffEvent N R := by
  ext y
  constructor
  · exact fun h => ⟨⟨h.1, fun i => ⟨(h.2 i).1, (h.2 i).2.trans_le hR⟩⟩,
      fun i => (h.2 i).2⟩
  · exact fun h => ⟨h.1.1, fun i => ⟨(h.1.2 i).1, h.2 i⟩⟩

lemma positive_cutoffNormalizer_pos (N : ℕ) {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) :
    0 < ∫ y in orderedChamber N (Ioo 0 R), density N y := by
  have h := positiveLaw_cutoff_pos N hR
  rw [positiveLaw_measureReal N (measurableSet_cutoffEvent N R),
    ← orderedChamber_eq_positive_cutoff N hR1] at h
  exact (div_pos_iff_of_pos_right (normalizer_pos N)).1 h

 

theorem positive_half_inverseQuarter_le_scaled_reference (N : ℕ) {β : ℝ} (hb : 4 ≤ β) :
    (∫ y in orderedChamber N (Ioo 0 (1 / 2 : ℝ)), inverseQuarterStatistic N y * density N y) /
        (∫ y in orderedChamber N (Ioo 0 (1 / 2 : ℝ)), density N y) ≤
      (∫ y in orderedChamber N (Ioo 0 (1 / 2 : ℝ)), inverseQuarterStatistic N y *
        scaledLaguerreDensity N (1 / 2) β y) /
      (∫ y in orderedChamber N (Ioo 0 (1 / 2 : ℝ)), scaledLaguerreDensity N (1 / 2) β y) := by
  let S := orderedChamber N (Ioo 0 (1 / 2 : ℝ))
  have hS := measurableSet_orderedChamber_Ioo N (1 / 2)
  have hSl : S ⊆ laguerreDomain N := fun _ hy => ⟨hy.1, fun i => (hy.2 i).1⟩
  have hSt : S ⊆ orderedDomain N := fun _ hy => ⟨hy.1, fun i =>
    ⟨(hy.2 i).1, (hy.2 i).2.trans (by norm_num)⟩⟩
  have heq : (fun y => scaledLaguerreDensity N (1 / 2) β y * upperLikelihood N β y) =ᵐ[volume.restrict S]
      density N := by
    filter_upwards [ae_restrict_mem hS] with y hy
    exact scaledDensity_mul_upperLikelihood β (fun i => (hy.2 i).1)
  have hiT := (integrableOn_density N).mono_set hSt
  have hiTF := (integrableOn_inverseQuarterSum_density N).mono_set hSt
  have hiB := (integrableOn_scaledLaguerreDensity (N := N) (by norm_num : (0 : ℝ) < 1/2)
    (by linarith : 1 ≤ β)).mono_set hSl
  have hiBF := (integrableOn_scaledLaguerre_inverseQuarter (N := N) (by norm_num : (1/4 : ℝ) < 1/2)
    (by linarith : 1 ≤ β)).mono_set hSl
  have heqF : (fun y => scaledLaguerreDensity N (1 / 2) β y *
      (-inverseQuarterStatistic N y * upperLikelihood N β y)) =ᵐ[volume.restrict S]
        (fun y => -(inverseQuarterStatistic N y * density N y)) := by
    filter_upwards [heq] with y hy
    calc
      _ = - (inverseQuarterStatistic N y * (scaledLaguerreDensity N (1/2) β y * upperLikelihood N β y)) := by ring
      _ = _ := by rw [hy]
  have h := ordered_density_covariance_Ioo (by norm_num : (0 : ℝ) < 1/2)
    (fun _ : Fin N => scaledLaguerreWeight (1 / 2) β)
    (fun _ => (continuousOn_scaledLaguerreWeight (1/2) β).mono (fun _ hx => hx.1))
    (fun _ _ hx => (scaledLaguerreWeight_pos (1/2) β hx.1).le)
    (fun y => -inverseQuarterStatistic N y) (upperLikelihood N β)
    ((continuousOn_inverseQuarterSum.mono (fun _ hx i => (hx i).1)).neg)
    ((continuousOn_upperLikelihood N β).mono (fun _ hx i => (hx i).1))
    (fun _ hx _ hy hxy => neg_le_neg (antitoneOn_inverseQuarterSum
      (fun i => (hx i).1) (fun i => (hy i).1) hxy)) (upperLikelihood_monotone N hb)
    hiB (by simpa only [Pi.neg_def, scaledLaguerreDensity, mul_neg, neg_mul, mul_comm] using hiBF.neg) (hiT.congr heq.symm)
    (hiTF.neg.congr heqF.symm)
  change _ ≤ _ at h
  have hprod : (∫ y in S, inverseQuarterStatistic N y * density N y) *
      (∫ y in S, scaledLaguerreDensity N (1/2) β y) ≤
      (∫ y in S, inverseQuarterStatistic N y * scaledLaguerreDensity N (1/2) β y) *
      (∫ y in S, density N y) := by
    change (∫ y in S, scaledLaguerreDensity N (1/2) β y * -inverseQuarterStatistic N y) *
      (∫ y in S, scaledLaguerreDensity N (1/2) β y * upperLikelihood N β y) ≤
      (∫ y in S, scaledLaguerreDensity N (1/2) β y) *
      (∫ y in S, scaledLaguerreDensity N (1/2) β y * (-inverseQuarterStatistic N y * upperLikelihood N β y)) at h
    rw [integral_congr_ae heq, integral_congr_ae heqF] at h
    simpa only [mul_neg, integral_neg, neg_mul, neg_le_neg_iff, mul_comm] using h
  exact (div_le_div_iff₀ (positive_cutoffNormalizer_pos N (by norm_num) (by norm_num))
    (scaledLaguerre_cutoffNormalizer_pos N (by norm_num) (by linarith) (by norm_num))).2 hprod

lemma integral_scaledLaguerre_cutoff (N : ℕ) (a R : ℝ) {β : ℝ} (hb : 0 < β) :
    laguerreDensityScale N a β *
      (∫ y in orderedChamber N (Ioo 0 R), scaledLaguerreDensity N a β y) =
      (β ^ N)⁻¹ * (∫ r in orderedChamber N (Ioo 0 (β * R)), laguerreDensity N a r) := by
  rw [← integral_const_mul]
  calc
    (∫ y in orderedChamber N (Ioo 0 R), laguerreDensityScale N a β * scaledLaguerreDensity N a β y) =
        ∫ y in orderedChamber N (Ioo 0 R), laguerreDensity N a (β • y) := by
      apply setIntegral_congr_fun (measurableSet_orderedChamber_Ioo N R)
      intro y hy
      exact (laguerreDensity_scaled a hb (fun i => (hy.2 i).1)).symm
    _ = _ := integral_orderedChamber_scaled R hb _

end
end CriticalStrip

end OAI
