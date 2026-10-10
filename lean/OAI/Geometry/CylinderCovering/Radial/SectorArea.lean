import OAI.Geometry.CylinderCovering.Angular.Caps

namespace OAI

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace AngularCaps

def radialDerivative (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (p.1 • ContinuousLinearMap.snd ℝ ℝ ℝ +
    p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem radialMap_hasFDerivAt (p : ℝ × ℝ) :
    HasFDerivAt radialMap (radialDerivative p) p := by
  exact ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.mul
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt).prodMk
      (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt

theorem radialDerivative_det (p : ℝ × ℝ) :
    (radialDerivative p : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)).det = p.2 := by
  have h : (radialDerivative p : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) =
      Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
        !![p.2, p.1; 0, 1] := by
    apply LinearMap.ext
    intro x
    simp [radialDerivative, Matrix.toLin_finTwoProd_apply, add_comm]
  rw [h, LinearMap.det_toLin, Matrix.det_fin_two]
  simp

theorem radialMap_injOn_positive :
    InjOn radialMap {p : ℝ × ℝ | 0 < p.2} := by
  intro x hx y hy hxy
  have hs : x.2 = y.2 := by simpa only [radialMap] using congrArg Prod.snd hxy
  have hq : x.1 * x.2 = y.1 * y.2 := by
    simpa only [radialMap] using congrArg Prod.fst hxy
  apply Prod.ext
  · rw [← hs] at hq
    exact mul_right_cancel₀ (ne_of_gt hx) hq
  · exact hs

theorem continuous_radialMap : Continuous radialMap := by
  unfold radialMap
  fun_prop

theorem isCompact_radialSector {l r : ℝ} {R : ℝ → ℝ}
    (hRcont : ContinuousOn R (Icc l r)) (hR : ∀ q ∈ Icc l r, 0 ≤ R q) :
    IsCompact (radialSector l r R) :=
  (isCompact_radialParameterSet hRcont hR).image continuous_radialMap

private theorem radialSector_eq_insert_positive {l r : ℝ} {R : ℝ → ℝ}
    (hlr : l ≤ r) (hR : ∀ q ∈ Icc l r, 0 ≤ R q) :
    radialSector l r R = insert (0, 0)
      (radialMap '' (radialParameterSet l r R ∩ {p : ℝ × ℝ | 0 < p.2})) := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    by_cases hs : x.2 = 0
    · left
      simp [radialMap, hs]
    · right
      exact ⟨x, ⟨hx, lt_of_le_of_ne hx.2.1 (Ne.symm hs)⟩, rfl⟩
  · rintro (rfl | ⟨x, hx, rfl⟩)
    · exact ⟨(l, 0), ⟨⟨le_rfl, hlr⟩, le_rfl, hR l ⟨le_rfl, hlr⟩⟩,
        by simp [radialMap]⟩
    · exact ⟨x, hx.1, rfl⟩

theorem radialSector_volume_eq_weighted_domain {l r : ℝ} {R : ℝ → ℝ}
    (hlr : l ≤ r) (hRcont : ContinuousOn R (Icc l r))
    (hR : ∀ q ∈ Icc l r, 0 ≤ R q) :
    volume (radialSector l r R) =
      ∫⁻ p in radialParameterSet l r R, ENNReal.ofReal p.2 := by
  let D := radialParameterSet l r R
  let Dpos := D ∩ {p : ℝ × ℝ | 0 < p.2}
  have hD : MeasurableSet D := (isCompact_radialParameterSet hRcont hR).measurableSet
  have hDpos : MeasurableSet Dpos := hD.inter (measurableSet_lt measurable_const measurable_snd)
  have hJac := lintegral_abs_det_fderiv_eq_addHaar_image (volume : Measure (ℝ × ℝ))
    hDpos (fun p _ => (radialMap_hasFDerivAt p).hasFDerivWithinAt)
    (radialMap_injOn_positive.mono inter_subset_right)
  have hJ : volume (radialMap '' Dpos) = ∫⁻ p in Dpos, ENNReal.ofReal p.2 := by
    rw [← hJac]
    apply setLIntegral_congr_fun hDpos
    intro p hp
    change ENNReal.ofReal |(radialDerivative p : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)).det| =
      ENNReal.ofReal p.2
    rw [radialDerivative_det, abs_of_pos hp.2]
  have hsector : volume (radialSector l r R) = volume (radialMap '' Dpos) := by
    rw [radialSector_eq_insert_positive hlr hR]
    rw [insert_eq, union_comm]
    exact measure_congr (union_ae_eq_left_of_ae_eq_empty (by simp))
  rw [hsector, hJ]
  rw [← lintegral_indicator hDpos, ← lintegral_indicator hD]
  apply lintegral_congr
  intro p
  by_cases hp : p ∈ D
  · by_cases hs : 0 < p.2
    · simp [Dpos, hp, hs]
    · have hz : p.2 = 0 := le_antisymm (le_of_not_gt hs) hp.2.1
      simp [Dpos, hp, hz]
  · simp [Dpos, hp]

private theorem lintegral_radial_id {a : ℝ} (ha : 0 ≤ a) :
    (∫⁻ s in Icc (0 : ℝ) a, ENNReal.ofReal s) = ENNReal.ofReal (a ^ 2 / 2) := by
  have hfi : IntegrableOn (fun s : ℝ => s) (Icc 0 a) := continuous_id.integrableOn_Icc
  have hnonneg : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) a)] (fun s : ℝ => s) :=
    (ae_restrict_mem measurableSet_Icc).mono (fun _ hs => hs.1)
  rw [← ofReal_integral_eq_lintegral_ofReal hfi hnonneg]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha, integral_id]
  norm_num

theorem weighted_radialParameterSet_integral {l r : ℝ} {R : ℝ → ℝ}
    (hRcont : ContinuousOn R (Icc l r)) (hR : ∀ q ∈ Icc l r, 0 ≤ R q) :
    (∫⁻ p in radialParameterSet l r R, ENNReal.ofReal p.2) =
      ∫⁻ q in Icc l r, ENNReal.ofReal ((R q) ^ 2 / 2) := by
  let D := radialParameterSet l r R
  have hD : MeasurableSet D := (isCompact_radialParameterSet hRcont hR).measurableSet
  rw [← lintegral_indicator hD, Measure.volume_eq_prod]
  rw [lintegral_prod _ ((measurable_snd.ennreal_ofReal).indicator hD).aemeasurable]
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro q
  by_cases hq : q ∈ Icc l r
  · have heq : (fun s : ℝ => D.indicator (fun p : ℝ × ℝ => ENNReal.ofReal p.2) (q, s)) =
        (Icc 0 (R q)).indicator (fun s : ℝ => ENNReal.ofReal s) := by
      funext s
      simp only [D, radialParameterSet, Set.indicator_apply, Set.mem_ofPred_eq,
        hq, true_and]
    rw [heq, lintegral_indicator measurableSet_Icc, lintegral_radial_id (hR q hq)]
    simp [hq]
  · have heq : (fun s : ℝ => D.indicator (fun p : ℝ × ℝ => ENNReal.ofReal p.2) (q, s)) = 0 := by
      funext s
      apply Set.indicator_of_notMem
      exact fun h => hq h.1
    rw [heq]
    change (∫⁻ s : ℝ, (0 : ENNReal)) = _
    simp [hq]

theorem radialSector_volume {l r : ℝ} {R : ℝ → ℝ}
    (hlr : l ≤ r) (hRcont : ContinuousOn R (Icc l r))
    (hR : ∀ q ∈ Icc l r, 0 ≤ R q) :
    volume (radialSector l r R) =
      ENNReal.ofReal (∫ q in l..r, (R q) ^ 2 / 2) := by
  rw [radialSector_volume_eq_weighted_domain hlr hRcont hR,
    weighted_radialParameterSet_integral hRcont hR]
  have hfi : IntegrableOn (fun q => (R q) ^ 2 / 2) (Icc l r) :=
    (hRcont.pow 2 |>.div_const 2).integrableOn_Icc
  have hnonneg : 0 ≤ᵐ[volume.restrict (Icc l r)] (fun q => (R q) ^ 2 / 2) :=
    Filter.Eventually.of_forall (fun _ => by positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal hfi hnonneg]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hlr]

end AngularCaps

end

end OAI
