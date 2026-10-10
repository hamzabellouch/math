import Mathlib
import OAI.Combinatorics.StripMass.WeightComparison

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators Pointwise
open Set MeasureTheory Filter
lemma integral_scaledLaguerre_cutoff_inverseQuarter (N : ℕ) (a R : ℝ) {β : ℝ} (hb : 0 < β) :
    (laguerreDensityScale N a β * (β ^ (1 / 4 : ℝ))⁻¹) *
      (∫ y in orderedChamber N (Ioo 0 R), inverseQuarterStatistic N y * scaledLaguerreDensity N a β y) =
      (β ^ N)⁻¹ * (∫ r in orderedChamber N (Ioo 0 (β * R)),
        inverseQuarterStatistic N r * laguerreDensity N a r) := by
  rw [← integral_const_mul]
  calc
    (∫ y in orderedChamber N (Ioo 0 R), (laguerreDensityScale N a β * (β ^ (1 / 4 : ℝ))⁻¹) *
        (inverseQuarterStatistic N y * scaledLaguerreDensity N a β y)) =
        ∫ y in orderedChamber N (Ioo 0 R), inverseQuarterStatistic N (β • y) *
          laguerreDensity N a (β • y) := by
      apply setIntegral_congr_fun (measurableSet_orderedChamber_Ioo N R)
      intro y hy
      dsimp only [inverseQuarterStatistic]
      rw [laguerreDensity_scaled a hb (fun i => (hy.2 i).1),
        inverseQuarterSum_smul hb (fun i => (hy.2 i).1)]
      ring
    _ = _ := integral_orderedChamber_scaled R hb
      (fun r => inverseQuarterStatistic N r * laguerreDensity N a r)

lemma laguerre_cutoffNormalizer_pos (N : ℕ) {a R : ℝ} (ha : 0 < a) (hR : 0 < R) :
    0 < ∫ r in orderedChamber N (Ioo 0 R), laguerreDensity N a r := by
  have h := laguerreLaw_cutoff_pos N ha hR
  rw [laguerreLaw_measureReal N ha (measurableSet_cutoffEvent N R),
    ← orderedChamber_eq_laguerre_cutoff] at h
  exact (div_pos_iff_of_pos_right (laguerreNormalizer_pos N ha)).1 h

lemma scaled_quotient {A Z B W c J p : ℝ} (hc : c ≠ 0) (hJ : J ≠ 0) (hp : p ≠ 0)
    (h0 : c * Z = J * W) (h1 : (c * p⁻¹) * A = J * B) :
    A / Z = p * (B / W) := by
  have hZ : Z = J * W / c := (eq_div_iff hc).2 (by simpa [mul_comm] using h0)
  have hA : A = J * B / (c * p⁻¹) := (eq_div_iff (mul_ne_zero hc (inv_ne_zero hp))).2
    (by simpa [mul_comm] using h1)
  rw [hZ, hA]
  field_simp

 

theorem scaled_reference_cutoff_inverseQuarter (N : ℕ) (a R : ℝ) {β : ℝ} (hb : 0 < β) :
    (∫ y in orderedChamber N (Ioo 0 R), inverseQuarterStatistic N y * scaledLaguerreDensity N a β y) /
      (∫ y in orderedChamber N (Ioo 0 R), scaledLaguerreDensity N a β y) =
      β ^ (1 / 4 : ℝ) *
        ((∫ r in orderedChamber N (Ioo 0 (β * R)), inverseQuarterStatistic N r * laguerreDensity N a r) /
          (∫ r in orderedChamber N (Ioo 0 (β * R)), laguerreDensity N a r)) := by
  exact scaled_quotient (laguerreDensityScale_pos N a hb).ne'
    (inv_ne_zero (pow_ne_zero _ hb.ne')) (Real.rpow_pos_of_pos hb _).ne'
    (integral_scaledLaguerre_cutoff N a R hb) (integral_scaledLaguerre_cutoff_inverseQuarter N a R hb)

lemma integral_positiveLaw_cutoff (N : ℕ) (R : ℝ) (f : (Fin N → ℝ) → ℝ) :
    (∫ y in cutoffEvent N R, f y ∂positiveLaw N) =
      (∫ y in orderedDomain N ∩ cutoffEvent N R, f y * density N y) / normalizer N := by
  rw [← integral_indicator (measurableSet_cutoffEvent N R), integral_positiveLaw N]
  unfold expectation
  simp_rw [← Set.indicator_mul_left]
  rw [setIntegral_indicator (measurableSet_cutoffEvent N R)]

lemma positiveLaw_conditioned_eq (N : ℕ) {R : ℝ} (hR : R ≤ 1) (f : (Fin N → ℝ) → ℝ) :
    (∫ y in cutoffEvent N R, f y ∂positiveLaw N) /
      (positiveLaw N).real (cutoffEvent N R) =
      (∫ y in orderedChamber N (Ioo 0 R), f y * density N y) /
        (∫ y in orderedChamber N (Ioo 0 R), density N y) := by
  rw [integral_positiveLaw_cutoff, positiveLaw_measureReal N (measurableSet_cutoffEvent N R),
    ← orderedChamber_eq_positive_cutoff N hR,
    div_div_div_cancel_right₀ (normalizer_pos N).ne']

lemma integral_laguerreLaw_cutoff (N : ℕ) {a : ℝ} (ha : 0 < a) (R : ℝ)
    (f : (Fin N → ℝ) → ℝ) :
    (∫ r in cutoffEvent N R, f r ∂laguerreLaw N a) =
      (∫ r in orderedChamber N (Ioo 0 R), f r * laguerreDensity N a r) / laguerreNormalizer N a := by
  rw [orderedChamber_eq_laguerre_cutoff, ← integral_indicator (measurableSet_cutoffEvent N R),
    integral_laguerreLaw N ha]
  unfold laguerreExpectation
  simp_rw [← Set.indicator_mul_left]
  rw [setIntegral_indicator (measurableSet_cutoffEvent N R)]

lemma laguerreLaw_conditioned_eq (N : ℕ) {a : ℝ} (ha : 0 < a) (R : ℝ)
    (f : (Fin N → ℝ) → ℝ) :
    (∫ r in cutoffEvent N R, f r ∂laguerreLaw N a) /
      (laguerreLaw N a).real (cutoffEvent N R) =
      (∫ r in orderedChamber N (Ioo 0 R), f r * laguerreDensity N a r) /
        (∫ r in orderedChamber N (Ioo 0 R), laguerreDensity N a r) := by
  rw [integral_laguerreLaw_cutoff N ha,
    laguerreLaw_measureReal N ha (measurableSet_cutoffEvent N R),
    ← orderedChamber_eq_laguerre_cutoff, div_div_div_cancel_right₀ (laguerreNormalizer_pos N ha).ne']

 

theorem positiveLaw_inverseQuarter_le_reference (N : ℕ) {β : ℝ} (hb : 4 ≤ β) :
    (∫ y, inverseQuarterStatistic N y ∂positiveLaw N) ≤
      β ^ (1 / 4 : ℝ) * (∫ r, inverseQuarterStatistic N r ∂laguerreLaw N (1 / 2)) /
        (laguerreLaw N (1 / 2)).real (cutoffEvent N (β / 2)) := by
  have hb0 : 0 < β := by linarith
  have hp := laguerreLaw_cutoff_pos N (by norm_num : (0:ℝ)<1/2) (by positivity : 0 < β / 2)
  have hcut : (∫ r in cutoffEvent N (β / 2), inverseQuarterStatistic N r ∂laguerreLaw N (1/2)) ≤
      ∫ r, inverseQuarterStatistic N r ∂laguerreLaw N (1/2) := by
    apply setIntegral_le_integral (integrable_laguerreLaw_inverseQuarterSum (by norm_num : (1/4:ℝ)<1/2))
    filter_upwards [ae_laguerreDomain N (1/2)] with r hr
    exact inverseQuarterStatistic_nonneg hr.2
  calc
    _ ≤ (∫ y in cutoffEvent N (1/2), inverseQuarterStatistic N y ∂positiveLaw N) /
        (positiveLaw N).real (cutoffEvent N (1/2)) := positiveLaw_cutoff_inverseQuarterSum (by norm_num)
    _ = (∫ y in orderedChamber N (Ioo 0 (1/2)), inverseQuarterStatistic N y * density N y) /
        (∫ y in orderedChamber N (Ioo 0 (1/2)), density N y) := positiveLaw_conditioned_eq N (by norm_num) _
    _ ≤ _ := positive_half_inverseQuarter_le_scaled_reference N hb
    _ = β ^ (1/4:ℝ) *
        ((∫ r in cutoffEvent N (β/2), inverseQuarterStatistic N r ∂laguerreLaw N (1/2)) /
          (laguerreLaw N (1/2)).real (cutoffEvent N (β/2))) := by
      rw [scaled_reference_cutoff_inverseQuarter N (1/2) (1/2) hb0,
        laguerreLaw_conditioned_eq N (by norm_num)]
      simp only [mul_one_div]
    _ ≤ _ := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hcut hp.le)
        (Real.rpow_pos_of_pos hb0 _).le


 


 
def mobiusMap (N : ℕ) (z : Fin N → ℝ) : Fin N → ℝ := fun i => mobiusCoordinate (z i)

lemma mobiusInverse_mem {y : ℝ} (hy : y ∈ Ioo 0 1) : y / (2 - y) ∈ Ioo 0 1 := by
  have hd : 0 < 2 - y := by linarith [hy.2]
  exact ⟨div_pos hy.1 hd, (div_lt_one hd).2 (by linarith [hy.2])⟩

lemma mobiusCoordinate_inverse {y : ℝ} (hy : y < 1) :
    mobiusCoordinate (y / (2 - y)) = y := by
  have hd : 2 - y ≠ 0 := by linarith
  unfold mobiusCoordinate
  field_simp
  ring

lemma inverse_mobiusCoordinate {z : ℝ} (hz : 0 < z) :
    mobiusCoordinate z / (2 - mobiusCoordinate z) = z := by
  have hd : 1 + z ≠ 0 := by positivity
  unfold mobiusCoordinate
  field_simp
  ring

lemma mobiusMap_mem {N : ℕ} {z : Fin N → ℝ} (hz : z ∈ orderedDomain N) :
    mobiusMap N z ∈ orderedDomain N := by
  exact ⟨fun i j hij => mobiusCoordinate_strictMonoOn (hz.2 i).1 (hz.2 j).1 (hz.1 hij),
    fun i => mobiusCoordinate_mem (hz.2 i)⟩

lemma mobiusMap_injOn (N : ℕ) : InjOn (mobiusMap N) (orderedDomain N) := by
  intro x hx y hy h
  funext i
  exact mobiusCoordinate_strictMonoOn.injOn (hx.2 i).1 (hy.2 i).1 (congrFun h i)

lemma mobiusMap_image (N : ℕ) : mobiusMap N '' orderedDomain N = orderedDomain N := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact mobiusMap_mem hx
  · intro y hy
    let x : Fin N → ℝ := fun i => y i / (2 - y i)
    have heq : mobiusMap N x = y := funext fun i => mobiusCoordinate_inverse (hy.2 i).2
    refine ⟨x, ⟨?_, fun i => mobiusInverse_mem (hy.2 i)⟩, heq⟩
    intro i j hij
    have h := hy.1 hij
    rw [← congrFun heq i, ← congrFun heq j] at h
    exact (mobiusCoordinate_strictMonoOn.lt_iff_lt (mobiusInverse_mem (hy.2 i)).1
      (mobiusInverse_mem (hy.2 j)).1).1 h

lemma hasDerivAt_mobiusCoordinate {z : ℝ} (hz : 0 < z) :
    HasDerivAt mobiusCoordinate (2 / (1 + z)^2) z := by
  have hd : (1 : ℝ) + id z ≠ 0 := by change 1 + z ≠ 0; positivity
  apply (((hasDerivAt_id z).const_mul 2).div ((hasDerivAt_id z).const_add 1) hd).congr_deriv
  simp only [id_eq, mul_one]
  ring

 
def mobiusDifferential (N : ℕ) (z : Fin N → ℝ) : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    (ContinuousLinearMap.toSpanSingleton ℝ (2 / (1 + z i)^2)).comp (ContinuousLinearMap.proj i)

lemma hasFDerivAt_mobiusMap {N : ℕ} {z : Fin N → ℝ} (hz : ∀ i, 0 < z i) :
    HasFDerivAt (mobiusMap N) (mobiusDifferential N z) z := by
  unfold mobiusMap mobiusDifferential
  rw [hasFDerivAt_pi]
  intro i
  have h1 : HasFDerivAt mobiusCoordinate
      (ContinuousLinearMap.toSpanSingleton ℝ (2 / (1 + z i)^2)) (z i) :=
    (hasDerivAt_mobiusCoordinate (hz i)).hasFDerivAt
  simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
    h1.comp z ((ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ).hasFDerivAt)

def mobiusJacobian (N : ℕ) (z : Fin N → ℝ) : ℝ := ∏ i, 2 / (1 + z i)^2

lemma det_mobiusDifferential (N : ℕ) (z : Fin N → ℝ) :
    (mobiusDifferential N z).det = mobiusJacobian N z := by
  simp only [mobiusDifferential, ContinuousLinearMap.det_pi,
    ContinuousLinearMap.det_toSpanSingleton, mobiusJacobian]

lemma mobiusJacobian_pos {N : ℕ} {z : Fin N → ℝ} (hz : ∀ i, 0 < z i) :
    0 < mobiusJacobian N z := by
  exact Finset.prod_pos fun i _ => div_pos (by norm_num) (sq_pos_of_pos (by linarith [hz i]))

 

theorem integral_mobiusMap (N : ℕ) (g : (Fin N → ℝ) → ℝ) :
    (∫ y in orderedDomain N, g y) =
      ∫ z in orderedDomain N, mobiusJacobian N z * g (mobiusMap N z) := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume
    (isOpen_orderedDomain N).measurableSet
    (fun z hz => (hasFDerivAt_mobiusMap (fun i => (hz.2 i).1)).hasFDerivWithinAt)
    (mobiusMap_injOn N) g
  rw [mobiusMap_image] at h
  apply h.trans
  apply setIntegral_congr_fun (isOpen_orderedDomain N).measurableSet
  intro z hz
  dsimp only
  rw [det_mobiusDifferential, abs_of_pos (mobiusJacobian_pos (fun i => (hz.2 i).1)), smul_eq_mul]

lemma integrableOn_mobiusMap_iff (N : ℕ) (g : (Fin N → ℝ) → ℝ) :
    IntegrableOn g (orderedDomain N) ↔
      IntegrableOn (fun z => mobiusJacobian N z * g (mobiusMap N z)) (orderedDomain N) := by
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    (isOpen_orderedDomain N).measurableSet
    (fun z hz => (hasFDerivAt_mobiusMap (fun i => (hz.2 i).1)).hasFDerivWithinAt)
    (mobiusMap_injOn N) g
  rw [mobiusMap_image] at h
  apply h.trans
  apply integrable_congr
  filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with z hz
  rw [det_mobiusDifferential, abs_of_pos (mobiusJacobian_pos (fun i => (hz.2 i).1)), smul_eq_mul]

lemma prod_pair_coordinates {N : ℕ} (f : Fin N → ℝ) :
    (∏ i, ∏ j ∈ Finset.Ioi i, f i * f j) = (∏ i, f i) ^ (N - 1) := by
  have h := Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag (fun i _ : Fin N => f i)
  simp only [mul_comm] at h
  rw [h]
  have heq (i : Fin N) : (∏ j ∈ ({i}ᶜ : Finset (Fin N)), f j) =
      ∏ j : Fin N, if i ≠ j then f j else 1 := by
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp [ne_comm]
  simp_rw [heq]
  rw [Finset.prod_comm]
  have heq' (j : Fin N) : (∏ i : Fin N, if i ≠ j then f j else 1) = f j ^ (N - 1) := by
    rw [← Finset.prod_filter]
    have hset : (Finset.univ.filter fun i : Fin N => i ≠ j) = {j}ᶜ := by
      ext i
      simp
    rw [hset]
    simp only [Finset.prod_const, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  simp_rw [heq']
  rw [Finset.prod_pow]

 
def mobiusDensityConstant (N : ℕ) : ℝ :=
  (∏ _ : Fin N, (2 : ℝ)) * ∏ i : Fin N, ∏ _j ∈ Finset.Ioi i, (2 : ℝ)

lemma mobiusDensityConstant_pos (N : ℕ) : 0 < mobiusDensityConstant N := by
  exact mul_pos (Finset.prod_pos fun _ _ => by norm_num)
    (Finset.prod_pos fun _ _ => Finset.prod_pos fun _ _ => by norm_num)

lemma prod_pairKernel_mobius {N : ℕ} {z : Fin N → ℝ} (hz : ∀ i, 0 < z i) :
    (∏ i, ∏ j ∈ Finset.Ioi i, pairKernel (mobiusCoordinate (z i)) (mobiusCoordinate (z j))) =
      (∏ i : Fin N, ∏ _j ∈ Finset.Ioi i, (2 : ℝ)) * (∏ i, ∏ j ∈ Finset.Ioi i, pairKernel (z i) (z j)) *
        (∏ i, ∏ j ∈ Finset.Ioi i, mobiusPairFactor (z i) (z j)) / (∏ i : Fin N, (1 + z i)) ^ (N - 1) := by
  have h (i j : Fin N) : pairKernel (mobiusCoordinate (z i)) (mobiusCoordinate (z j)) =
      2 * pairKernel (z i) (z j) * mobiusPairFactor (z i) (z j) / ((1 + z i) * (1 + z j)) := by
    rw [pairKernel_mobius (hz i) (hz j)]
    simp only [mobiusPairFactor, div_eq_mul_inv, mul_inv_rev]
    ring
  simp_rw [h, Finset.prod_div_distrib, Finset.prod_mul_distrib]
  have hd := prod_pair_coordinates (fun i => 1 + z i)
  simp only [Finset.prod_mul_distrib] at hd
  rw [hd]

lemma scaledWeight_mul_lowerLikelihoodWeight (N : ℕ) (β z : ℝ) :
    scaledLaguerreWeight 1 β z * lowerLikelihoodWeight N β z =
      omega (mobiusCoordinate z) / (1 + z) ^ (N + 1) := by
  unfold scaledLaguerreWeight lowerLikelihoodWeight
  norm_num only [sub_self, Real.rpow_zero, one_mul]
  calc
    _ = omega (mobiusCoordinate z) / (1 + z) ^ (N + 1) *
        (Real.exp (-(β * z)) * Real.exp (β * z)) := by ring
    _ = _ := by rw [← Real.exp_add]; simp

lemma scaledDensity_mul_lowerLikelihood (N : ℕ) (β : ℝ) (z : Fin N → ℝ) :
    scaledLaguerreDensity N 1 β z * lowerLikelihood N β z =
      (∏ i, omega (mobiusCoordinate (z i))) / (∏ i : Fin N, (1 + z i)) ^ (N + 1) *
        (∏ i, ∏ j ∈ Finset.Ioi i, pairKernel (z i) (z j)) *
        (∏ i, ∏ j ∈ Finset.Ioi i, mobiusPairFactor (z i) (z j)) := by
  have hw : (∏ i, scaledLaguerreWeight 1 β (z i)) *
      (∏ i, lowerLikelihoodWeight N β (z i)) =
        (∏ i, omega (mobiusCoordinate (z i))) / (∏ i : Fin N, (1 + z i)) ^ (N + 1) := by
    rw [← Finset.prod_mul_distrib]
    simp_rw [scaledWeight_mul_lowerLikelihoodWeight,
      Finset.prod_div_distrib, Finset.prod_pow]
  unfold scaledLaguerreDensity rawProductDensity lowerLikelihood
  change ((∏ i, scaledLaguerreWeight 1 β (z i)) * _) * ((∏ i, lowerLikelihoodWeight N β (z i)) * _) = _
  rw [mul_mul_mul_comm, hw]
  have hI (i : Fin N) : Finset.univ.filter (i < ·) = Finset.Ioi i := by ext j; simp
  simp_rw [hI]
  ring

 

theorem density_mobiusMap {N : ℕ} (β : ℝ) {z : Fin N → ℝ} (hz : ∀ i, 0 < z i) :
    mobiusJacobian N z * density N (mobiusMap N z) =
      mobiusDensityConstant N * (scaledLaguerreDensity N 1 β z * lowerLikelihood N β z) := by
  cases N with
  | zero => simp [mobiusJacobian, density, mobiusDensityConstant,
      scaledLaguerreDensity, rawProductDensity, lowerLikelihood]
  | succ n =>
    rw [scaledDensity_mul_lowerLikelihood]
    unfold density mobiusMap mobiusJacobian mobiusDensityConstant
    simp only [Finset.prod_div_distrib, Finset.prod_pow]
    rw [prod_pairKernel_mobius hz]
    simp only [Nat.add_sub_cancel]
    have hd : (∏ i : Fin (n + 1), (1 + z i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => by linarith [hz i]
    field_simp
    ring

lemma jacobian_weighted_density {N : ℕ} (β : ℝ) (g : (Fin N → ℝ) → ℝ)
    {z : Fin N → ℝ} (hz : z ∈ orderedDomain N) :
    mobiusJacobian N z * (g (mobiusMap N z) * density N (mobiusMap N z)) =
      mobiusDensityConstant N * (scaledLaguerreDensity N 1 β z *
        (g (mobiusMap N z) * lowerLikelihood N β z)) := by
  calc
    _ = g (mobiusMap N z) * (mobiusJacobian N z * density N (mobiusMap N z)) := by ring
    _ = _ := by rw [density_mobiusMap β (fun i => (hz.2 i).1)]; ring

lemma integral_density_mobius_likelihood (N : ℕ) (β : ℝ) (g : (Fin N → ℝ) → ℝ) :
    (∫ y in orderedDomain N, g y * density N y) =
      mobiusDensityConstant N * ∫ z in orderedDomain N,
        scaledLaguerreDensity N 1 β z * (g (mobiusMap N z) * lowerLikelihood N β z) := by
  rw [integral_mobiusMap, ← integral_const_mul]
  exact setIntegral_congr_fun (isOpen_orderedDomain N).measurableSet
    (fun z hz => jacobian_weighted_density β g hz)

lemma integrableOn_density_mobius_likelihood_iff (N : ℕ) (β : ℝ) (g : (Fin N → ℝ) → ℝ) :
    IntegrableOn (fun y => g y * density N y) (orderedDomain N) ↔
      IntegrableOn (fun z => scaledLaguerreDensity N 1 β z *
        (g (mobiusMap N z) * lowerLikelihood N β z)) (orderedDomain N) := by
  rw [integrableOn_mobiusMap_iff]
  have heq : (fun z => mobiusJacobian N z * (g (mobiusMap N z) * density N (mobiusMap N z)))
      =ᵐ[volume.restrict (orderedDomain N)]
      (fun z => mobiusDensityConstant N * (scaledLaguerreDensity N 1 β z *
        (g (mobiusMap N z) * lowerLikelihood N β z))) := by
    filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with z hz
    exact jacobian_weighted_density β g hz
  unfold IntegrableOn
  rw [integrable_congr heq]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (mobiusDensityConstant_pos N).ne') _

lemma mobiusLikelihood_Normalizer (N : ℕ) (β : ℝ) :
    normalizer N = mobiusDensityConstant N *
      ∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z * lowerLikelihood N β z := by
  simpa only [one_mul, normalizer] using integral_density_mobius_likelihood N β (fun _ => 1)

lemma integrableOn_mobiusLikelihood (N : ℕ) (β : ℝ) :
    IntegrableOn (fun z => scaledLaguerreDensity N 1 β z * lowerLikelihood N β z) (orderedDomain N) := by
  simpa only [one_mul] using
    (integrableOn_density_mobius_likelihood_iff N β (fun _ => 1)).1
      (by simpa only [one_mul] using integrableOn_density N)

lemma mobiusLikelihood_Normalizer_pos (N : ℕ) (β : ℝ) :
    0 < ∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z * lowerLikelihood N β z := by
  have h := normalizer_pos N
  rw [mobiusLikelihood_Normalizer N β] at h
  exact (mul_pos_iff_of_pos_left (mobiusDensityConstant_pos N)).1 h

lemma continuousOn_mobiusCoordinate : ContinuousOn mobiusCoordinate (Ioi 0) := by
  exact (continuous_const.mul continuous_id).continuousOn.div
    (continuous_const.add continuous_id).continuousOn (fun z hz => (add_pos (by norm_num : (0:ℝ) < 1) hz).ne')

lemma continuousOn_lowerLikelihood (N : ℕ) (β : ℝ) :
    ContinuousOn (lowerLikelihood N β) (coordinateBox (Fin N) (Ioo 0 1)) := by
  unfold lowerLikelihood
  apply ContinuousOn.mul
  · apply continuousOn_finsetProd
    intro i _
    have hmob : ContinuousOn (fun z : Fin N → ℝ => mobiusCoordinate (z i))
        (coordinateBox (Fin N) (Ioo 0 1)) :=
      continuousOn_mobiusCoordinate.comp (continuous_apply i).continuousOn (fun z hz => (hz i).1)
    exact (continuousOn_omega_Ioi.comp hmob (fun z hz => (mobiusCoordinate_mem (hz i)).1)).mul
      ((Real.continuous_exp.comp (continuous_const.mul (continuous_apply i))).continuousOn.div
        ((continuous_const.add (continuous_apply i)).pow (N + 1)).continuousOn
        (fun z hz => pow_ne_zero _ (by linarith [(hz i).1])))
  · apply continuousOn_finsetProd
    intro i _
    apply continuousOn_finsetProd
    intro j _
    have hq : ContinuousOn (fun z : Fin N → ℝ => 2 * z i * z j / (z i + z j))
        (coordinateBox (Fin N) (Ioo 0 1)) :=
      ((continuous_const.mul (continuous_apply i)).mul (continuous_apply j)).continuousOn.div
        ((continuous_apply i).add (continuous_apply j)).continuousOn
        (fun z hz => (add_pos (hz i).1 (hz j).1).ne')
    exact (continuousOn_const.add hq).inv₀ (fun z hz =>
      (add_pos (by norm_num : (0:ℝ)<1)
        (div_pos (mul_pos (mul_pos (by norm_num) (hz i).1) (hz j).1)
          (add_pos (hz i).1 (hz j).1))).ne')

lemma mobiusCoordinate_le_double {z : ℝ} (hz : 0 < z) : mobiusCoordinate z ≤ 2 * z := by
  apply (div_le_iff₀ (by linarith : 0 < 1 + z)).2
  nlinarith [sq_nonneg z]

lemma self_le_mobiusCoordinate {z : ℝ} (hz : z ∈ Ioo 0 1) : z ≤ mobiusCoordinate z := by
  apply (le_div_iff₀ (by linarith [hz.1] : 0 < 1 + z)).2
  nlinarith [mul_nonneg hz.1.le (sub_nonneg.mpr hz.2.le)]

lemma mobius_inverseQuarter_bounds {z : ℝ} (hz : z ∈ Ioo 0 1) :
    (2 : ℝ) ^ (-(1/4:ℝ)) * z ^ (-(1/4:ℝ)) ≤ (mobiusCoordinate z) ^ (-(1/4:ℝ)) ∧
    (mobiusCoordinate z) ^ (-(1/4:ℝ)) ≤ z ^ (-(1/4:ℝ)) := by
  constructor
  · rw [← Real.mul_rpow (by norm_num : (0:ℝ)≤2) hz.1.le]
    exact Real.rpow_le_rpow_of_nonpos (mobiusCoordinate_mem hz).1
      (mobiusCoordinate_le_double hz.1) (by norm_num)
  · exact Real.rpow_le_rpow_of_nonpos hz.1 (self_le_mobiusCoordinate hz) (by norm_num)

end
end CriticalStrip

end OAI
