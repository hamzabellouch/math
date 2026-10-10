import Mathlib
import OAI.Analysis.CoulombIonization.Variational.ActualSectorPlateau
import OAI.Analysis.CoulombIonization.RadialBounds.CellCountAbsorptionBarrier
import OAI.Analysis.CoulombIonization.Localization.CanonicalRealPacketBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_UnshiftedCellCount_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

namespace CoulombAtom

 def universalCellCountConstant : ℝ := cellUniversalCountConstant (packetDirichlet canonicalRealPacket)
lemma universalCellCountConstant_one_le : 1 ≤ universalCellCountConstant :=
  cellUniversalCountConstant_one_le (packetDirichlet_nonneg _)

 theorem priced_local_cell_count {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {y : Space} (hy : y ≠ 0) : rawCountMoment ψ y (localCellRadius y) ≤
      universalCellCountConstant*(localOffsetMass (max (corePriceExcess Z lam ψ) 0) y)^2 := by
  have hh := priced_cell_supremum_bound hψ hm hZ hlam canonicalRealPacket_smooth
    canonicalRealPacket_compact canonicalRealPacket_normalized canonicalRealPacket_radial canonicalRealPacket_support
  exact (localCountMoment_le_supremum hψ.sobolevVector _ hy).trans
    (mul_le_mul_of_nonneg_right hh (sq_nonneg _))

lemma localOffsetMass_mono {D E : ℝ} (h : D ≤ E) (y : Space) :
    localOffsetMass D y ≤ localOffsetMass E y := by
  unfold localOffsetMass
  gcongr
  exact div_nonneg (norm_nonneg _) (by norm_num)

lemma quantum_unpriced_le_price (Z : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    sInf (Set.range (energy (Z:ℝ))) ≤ priceEnergy (energy Z) lam := by
  obtain ⟨n,hn⟩ := quantum_exists_priceMinimizes (Nat.cast_nonneg Z) hlam
  rw [priceEnergy_eq_of_minimizes hn,quantum_unpriced_infimum_finite]
  have hh := quantum_energy_coarse_fence_minimum Z n
  have hp : 0 ≤ lam*(n:ℝ) := mul_nonneg hlam.le (Nat.cast_nonneg n)
  linarith only [hh,hp]

lemma unshifted_priced_excess_bound (Z : ℕ) {N : ℕ} {ψ : FormVector N}
    (hm : formMass ψ = 1) {D lam : ℝ} (hlam : 0 < lam)
    (he : formEnergy Z ψ ≤ sInf (Set.range (energy (Z:ℝ)))+D) :
    corePriceExcess Z lam ψ ≤ D+lam*N := by
  have hp := quantum_unpriced_le_price Z hlam
  rw [corePriceExcess,hm,mul_one,mul_one]
  linarith only [hp,he]

 theorem unshifted_local_cell_count (Z : ℕ) {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) {D : ℝ} (hD : 0 ≤ D)
    (he : formEnergy Z ψ ≤ sInf (Set.range (energy (Z:ℝ)))+D)
    {y : Space} (hy : y ≠ 0) : rawCountMoment ψ y (localCellRadius y) ≤
      universalCellCountConstant*(localOffsetMass D y)^2 := by
  have hC : 0 ≤ universalCellCountConstant := le_trans zero_le_one universalCellCountConstant_one_le
  have hh (lam : ℝ) (hlam : 0 < lam) : rawCountMoment ψ y (localCellRadius y) ≤
      universalCellCountConstant*(localOffsetMass (D+lam*N) y)^2 := by
    have hex := unshifted_priced_excess_bound Z hm hlam he
    have hz : 0 ≤ D+lam*(N:ℝ) := by positivity
    have hm' := localOffsetMass_mono (max_le hex hz) y
    have hsq := pow_le_pow_left₀ (le_trans zero_le_one (localOffsetMass_one_le _ _)) hm' 2
    exact (priced_local_cell_count hψ hm (Nat.cast_nonneg Z) hlam hy).trans
      (mul_le_mul_of_nonneg_left hsq hC)
  let eps (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have hp (n : ℕ) : 0 < eps n := by dsimp [eps]; positivity
  have ht : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : Continuous (fun t : ℝ => universalCellCountConstant*(localOffsetMass (D+t*N) y)^2) := by
    unfold localOffsetMass
    fun_prop
  have ht' : Tendsto (fun n => universalCellCountConstant*(localOffsetMass (D+eps n*N) y)^2)
      atTop (𝓝 (universalCellCountConstant*(localOffsetMass D y)^2)) := by
    simpa only [Function.comp_def,zero_mul,add_zero] using hc.continuousAt.tendsto.comp ht
  exact ge_of_tendsto ht' (Eventually.of_forall (fun n => hh (eps n) (hp n)))

 theorem unshifted_local_count_supremum (Z : ℕ) {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) {D : ℝ} (hD : 0 ≤ D)
    (he : formEnergy Z ψ ≤ sInf (Set.range (energy (Z:ℝ)))+D) :
    localCountSupremum ψ D ≤ universalCellCountConstant :=
  localCountSupremum_le D universalCellCountConstant_one_le (fun _ hy => unshifted_local_cell_count Z hψ hm hD he hy)

end CoulombAtom

end Work_UnshiftedCellCount_barrier_scope

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped BigOperators Topology

namespace CoulombBarrier
open CoulombAtom CoulombObservation
attribute [local instance] physicalObservationLaw_probability
attribute [local irreducible] masterWidth masterKernel originalRawKernel physicalObservationLaw
  originalDatum jointMasterPosterior

lemma masterKernel_amplitude {g : Space → ℝ} (hg : Continuous g)
    (hgs : tsupport g ⊆ ball 0 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {c₁ r₀ s : ℝ},
      0 < c₁ → c₁ < (10*(100000:ℝ))⁻¹ → 0 < r₀ → 0 < s → s ≤ 1 →
      ∀ x y, masterKernel c₁ r₀ s g x y ≤ A*(masterWidth c₁ r₀ s y)⁻¹^3 := by
  have hcg : HasCompactSupport g :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space) 1)
      (fun x hx => ball_subset_closedBall (hgs (subset_tsupport g hx)))
  obtain ⟨z,hz⟩ := (hg.pow 2).norm.exists_forall_ge_of_hasCompactSupport (hcg.mul_left).norm
  let B := ‖(g z)^2‖
  have hB : 0 ≤ B := norm_nonneg _
  refine ⟨8*B,by positivity,?_⟩
  intro c₁ r₀ s hc hcL hr hs hs1 x y
  rw [masterKernel_eq_widthKernel hc hr hs g]
  have he := congrFun (widthKernel_clamp (masterWidth_small_lipschitz hc hcL hr hs hs1)
    (masterWidth_pos hc hr hs) (by norm_num) (masterProfile_support hgs) y) x
  rw [he,widthKernel]
  have hp := masterWidth_pos hc hr hs y
  have hi : (max (masterWidth c₁ r₀ s x) (masterWidth c₁ r₀ s y/2))⁻¹ ≤
      (masterWidth c₁ r₀ s y/2)⁻¹ := inv_anti₀ (half_pos hp) (le_max_right _ _)
  have hgB : (g ((max (masterWidth c₁ r₀ s x) (masterWidth c₁ r₀ s y/2))⁻¹ • (y-x)))^2 ≤ B := by
    exact (le_abs_self _).trans (hz _)
  have hi0 : 0 ≤ (max (masterWidth c₁ r₀ s x) (masterWidth c₁ r₀ s y/2))⁻¹ :=
    inv_nonneg.mpr ((half_pos hp).le.trans (le_max_right _ _))
  calc
    _ ≤ (masterWidth c₁ r₀ s y/2)⁻¹^3*B :=
      mul_le_mul (pow_le_pow_left₀ hi0 hi 3) hgB (sq_nonneg _) (by positivity)
    _ = _ := by rw [inv_div]; ring

lemma masterWidth_radius_lower {c₁ r₀ s r : ℝ} (hc : 0 ≤ c₁) (hr : 0 < r)
    (hrs : r ≤ s) {y : Space} (hy : r ≤ ‖y‖) :
    c₁*r^(1+masterExponent) ≤ masterWidth c₁ r₀ s y := by
  have hd : r ≤ masterBaseDistance r₀ y := hy.trans (le_max_left _ _)
  have hm : r ≤ min (masterBaseDistance r₀ y) s := le_min hd hrs
  rw [masterWidth,Real.rpow_add hr]
  simp only [Real.rpow_one]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (mul_le_mul hd (Real.rpow_le_rpow hr.le hm masterExponent_nonneg)
      (Real.rpow_nonneg hr.le _) (hr.le.trans hd)) hc

lemma masterWidth_radius_upper {c₁ r₀ s r : ℝ} (hc : 0 ≤ c₁)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (hrr : r₀ ≤ r)
    {y : Space} (hy : r ≤ ‖y‖) (hy2 : ‖y‖ ≤ 2*r) :
    masterWidth c₁ r₀ s y ≤ 2*c₁*r := by
  have hm : masterBaseDistance r₀ y = ‖y‖ := max_eq_left (hrr.trans hy)
  have hb := masterWidth_upper hc hr₀ hs y
  rw [hm] at hb
  have hpow := Real.rpow_le_one hs.le hs1 masterExponent_nonneg
  calc
    _ ≤ c₁*‖y‖*s^masterExponent := hb
    _ ≤ c₁*‖y‖*1 := mul_le_mul_of_nonneg_left hpow (mul_nonneg hc (norm_nonneg _))
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hy2 hc]

def rawAnnularCount {N : ℕ} (a b : ℝ) (x : Configuration N) : ℝ :=
  ∑ i, if a ≤ ‖x i‖ ∧ ‖x i‖ ≤ b then 1 else 0

lemma rawAnnularCount_nonneg {N : ℕ} (a b : ℝ) (x : Configuration N) :
    0 ≤ rawAnnularCount a b x := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> norm_num

lemma rawAnnularCount_le {N : ℕ} (a b : ℝ) (x : Configuration N) :
    rawAnnularCount a b x ≤ N := by
  calc
    _ ≤ ∑ _ : Fin N, (1:ℝ) := Finset.sum_le_sum fun i _ => by split_ifs <;> norm_num
    _ = N := by simp

lemma rawAnnularCount_measurable {N : ℕ} (a b : ℝ) :
    Measurable (rawAnnularCount (N := N) a b) := by
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.ite
    ((isClosed_le continuous_const (continuous_apply i).norm).inter
      (isClosed_le (continuous_apply i).norm continuous_const)).measurableSet measurable_const

lemma rawBallCount_le_annular {N : ℕ} {y : Space} {r R : ℝ}
    (_hr : 0 ≤ r) (hy : r ≤ ‖y‖) (hy2 : ‖y‖ ≤ 2*r) (hR : R ≤ r/2)
    (x : Configuration N) : rawBallCount y R x ≤ rawAnnularCount (r/2) (3*r) x := by
  apply Finset.sum_le_sum
  intro i _
  split_ifs with h hA hA
  · norm_num
  · exfalso
    apply hA
    have hxy : ‖x i-y‖ ≤ r/2 := h.le.trans hR
    have hlo := norm_sub_norm_le y (x i)
    rw [norm_sub_rev y (x i)] at hlo
    have hup := norm_sub_norm_le (x i) y
    constructor <;> linarith
  · norm_num
  · norm_num

end CoulombBarrier

end

end OAI
