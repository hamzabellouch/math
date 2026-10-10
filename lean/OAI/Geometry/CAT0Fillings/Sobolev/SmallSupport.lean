import Mathlib
import OAI.Geometry.CAT0Fillings.Gradient.HilbertAtlas
import OAI.Geometry.CAT0Fillings.Mass.IntrinsicCoarea
import OAI.Geometry.CAT0Fillings.Rearrangement.Sobolev

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.Rearrangement

lemma positive_tail_right (μ : Measure ℝ) [IsFiniteMeasure μ] {t : ℝ}
    (ht : 0 < μ.real (Ioi t)) : ∃ s : ℝ, t < s ∧ 0 < μ.real (Ioi s) := by
  have h := (negativeTail μ).right_continuous' t
  have hc : ContinuousWithinAt (fun s => μ.real (Ioi s)) (Ici t) t := by
    have h := h.neg
    change ContinuousWithinAt (fun s => - -μ.real (Ioi s)) (Ici t) t at h
    simpa only [neg_neg] using h
  have hp : ∀ᶠ s in 𝓝[>] t, 0 < μ.real (Ioi s) :=
    (hc.mono Ioi_subset_Ici_self) (isOpen_Ioi.mem_nhds ht)
  have he : ∀ᶠ s in 𝓝[>] t, t < s ∧ 0 < μ.real (Ioi s) := by
    filter_upwards [self_mem_nhdsWithin,hp] with s hs hp
    exact ⟨hs,hp⟩
  exact he.exists

theorem exists_essential_top (μ : Measure ℝ) [IsFiniteMeasure μ] {B : ℝ}
    (hB : μ (Ioi B) = 0) (hzero : 0 < μ.real (Ioi 0)) :
    ∃ U : ℝ, 0 < U ∧ μ (Ioi U) = 0 ∧ ∀ t ∈ Ico 0 U, 0 < μ.real (Ioi t) := by
  let S := {t : ℝ | 0 < μ.real (Ioi t)}
  have hS : S.Nonempty := ⟨0,hzero⟩
  have hbd : BddAbove S := by
    refine ⟨B,fun t ht => ?_⟩
    by_contra hn
    have he := measure_mono_null (Ioi_subset_Ioi (not_le.mp hn).le) hB
    have : μ.real (Ioi t) = 0 := by rw [measureReal_def,he,ENNReal.toReal_zero]
    exact ht.ne' this
  let U := sSup S
  have hU : 0 < U := by
    obtain ⟨t,ht,htp⟩ := positive_tail_right μ hzero
    exact ht.trans_le (le_csSup hbd htp)
  have hupper : μ (Ioi U) = 0 := by
    by_contra hm
    have hu : 0 < μ.real (Ioi U) := ENNReal.toReal_pos_iff.mpr
      ⟨pos_iff_ne_zero.mpr hm,measure_lt_top _ _⟩
    obtain ⟨t,ht,htp⟩ := positive_tail_right μ hu
    exact ht.not_ge (le_csSup hbd htp)
  refine ⟨U,hU,hupper,fun t ht => ?_⟩
  obtain ⟨s,hs,hst⟩ := exists_lt_of_lt_csSup hS ht.2
  exact hs.trans_le (measureReal_mono (Ioi_subset_Ioi hst.le))

end CAT0Fillings.Rearrangement
end

section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open BorelRestriction MassMeasure Rearrangement RadialSobolev

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem small_support_sobolev {k : ℕ} (hk : 0 < k)
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
    (hX : IsCAT0 X) (q : ChartGeometry hT.1)
    {δ η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hiso : ∀ E : Set X, MeasurableSet E →
      IsIntegral (k+2) (restrictCurrent hT.1 E) → mass (restrictCurrent hT.1 E) ≤ δ →
      (1-η)*mass (restrictCurrent hT.1 E) ≤
        fillingCoefficient (k+1)*(mass (boundarySucc (restrictCurrent hT.1 E)))^(fillingPower (k+1)))
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) (hu0 : ∀ x, 0 ≤ u x)
    (hsupp : (currentMassMeasure hT.1).real {x | 0 < u x} ≤ δ) :
    (k+2:ℝ)*(sphereArea (k+2))^(2/(k+2:ℝ)) *
      ((∫⁻ x, ENNReal.ofReal ((u x)^(sobolevP (k+2))) ∂currentMassMeasure hT.1).toReal)^(2/sobolevP (k+2)) ≤
      4/((k+2:ℝ)-2)*((1-η)⁻¹)^2*(q.energyMeasure u).real univ := by
  let μ := (currentMassMeasure hT.1).map u
  let ζ := (q.energyMeasure u).map u
  let := q.energyMeasure_finite hu
  have hμfin : IsFiniteMeasure μ := inferInstance
  have hζfin : IsFiniteMeasure ζ := inferInstance
  have hn : 2 < k+2 := by omega
  have hp := (sobolev_exponents hn).1
  have hneg : ∀ᵐ t ∂μ, 0 ≤ t := by
    exact (ae_map_iff hu.continuous.measurable.aemeasurable (by measurability)).mpr
      (Eventually.of_forall hu0)
  have htail (t : ℝ) : μ.real (Ioi t) = mass (restrictCurrent hT.1 {x | t < u x}) := by
    rw [restriction_mass hT.1 (measurableSet_lt measurable_const hu.continuous.measurable)]
    simp only [μ,measureReal_def,Measure.map_apply hu.continuous.measurable measurableSet_Ioi]
    rfl
  have hmoment : (∫⁻ t, ENNReal.ofReal (t^(sobolevP (k+2))) ∂μ) =
      ∫⁻ x, ENNReal.ofReal ((u x)^(sobolevP (k+2))) ∂currentMassMeasure hT.1 := by
    exact lintegral_map (by fun_prop) hu.continuous.measurable
  have hζ : ζ.real univ = (q.energyMeasure u).real univ := by
    simp only [ζ,measureReal_def,Measure.map_apply hu.continuous.measurable MeasurableSet.univ,preimage_univ]
  by_cases hzero : μ (Ioi 0) = 0
  · have hzv : ∀ᵐ t ∂μ, t = 0 := by
      have hh : ∀ᵐ t ∂μ, t ∉ Ioi (0:ℝ) := (ae_iff.mpr (by simpa only [not_not,ofPred_mem_eq] using hzero))
      filter_upwards [hneg,hh] with t ht hh
      exact le_antisymm (le_of_not_gt hh) ht
    have hmom : (∫⁻ t, ENNReal.ofReal (t^(sobolevP (k+2))) ∂μ) = 0 := by
      calc
        _ = ∫⁻ _ : ℝ, (0 : ℝ≥0∞) ∂μ := lintegral_congr_ae (hzv.mono fun t ht => by
          rw [ht,Real.zero_rpow hp.ne',ENNReal.ofReal_zero])
        _ = 0 := lintegral_zero
    rw [←hmoment,hmom,ENNReal.toReal_zero,Real.zero_rpow (div_pos (by norm_num) hp).ne',mul_zero]
    have hm : 0 ≤ (q.energyMeasure u).real univ := measureReal_nonneg
    have hkR : (0:ℝ) < k := by exact_mod_cast hk
    exact mul_nonneg (mul_nonneg (div_nonneg (by norm_num) (by linarith)) (sq_nonneg _)) measureReal_nonneg
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hu.continuous.continuousOn
  have hbd : μ (Ioi B) = 0 := by
    rw [Measure.map_apply hu.continuous.measurable measurableSet_Ioi]
    have he : u ⁻¹' Ioi B = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (le_trans (le_abs_self _) (by simpa only [Real.norm_eq_abs] using hB x (mem_univ x))).not_gt hx
    rw [he,measure_empty]
  obtain ⟨U,hU,hupper,hpos⟩ := exists_essential_top μ hbd
    (ENNReal.toReal_pos_iff.mpr ⟨pos_iff_ne_zero.mpr hzero,measure_lt_top _ _⟩)
  have hco := q.ae_intrinsic_coarea hT hz hX hu
  have hco' : ∀ᵐ t ∂volume.restrict (Ioo 0 U),
      (1-η)*((k+2:ℝ)*omega (k+2)*(radiusDistribution μ (omega (k+2)) (k+2) t)^(k+2-1)) ≤
        mass (boundarySucc (restrictCurrent hT.1 {x | t < u x})) ∧
      mass (boundarySucc (restrictCurrent hT.1 {x | t < u x})) ≤
        ((K:ℝ)+1)*(μ.rnDeriv volume t).toReal ∧
      mass (boundarySucc (restrictCurrent hT.1 {x | t < u x}))^2 ≤
        (μ.rnDeriv volume t).toReal*(ζ.rnDeriv volume t).toReal := by
    filter_upwards [hco.filter_mono ae_restrict_le,ae_restrict_mem measurableSet_Ioo] with t ht hti
    have hE : MeasurableSet {x | t < u x} := measurableSet_lt measurable_const hu.continuous.measurable
    have hsmall : mass (restrictCurrent hT.1 {x | t < u x}) ≤ δ := by
      rw [restriction_mass hT.1 hE]
      exact (measureReal_mono (fun x hx => hti.1.trans hx)).trans hsupp
    have hi := hiso _ hE ht.1 hsmall
    have hr := radius_nonneg μ (n := k+2) (omega_pos (by omega : 0 < k+2)).le t
    have he := radius_pow μ (omega_pos (by omega : 0 < k+2)) (by omega : 0 < k+2) t
    have hib : (1-η)*(omega (k+2)*(radiusDistribution μ (omega (k+2)) (k+2) t)^(k+2)) ≤
        fillingCoefficient (k+1)*(mass (boundarySucc (restrictCurrent hT.1 {x | t < u x})))^(fillingPower (k+1)) := by
      rw [he,htail]
      exact hi
    have hper := perimeter_of_small_isoperimetry (by omega : 0 < k+1) hr
      (mass_nonneg _) hη hη1 hib
    refine ⟨?_,?_,ht.2.1⟩
    · simpa only [Nat.add_assoc, show (1:ℕ)+1=2 from rfl, show k+2-1=k+1 by omega,
        Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, show (1:ℝ)+1=2 by norm_num] using hper
    · exact ht.2.2.trans (mul_le_mul_of_nonneg_right (by linarith) ENNReal.toReal_nonneg)
  have hs := rearranged_sobolev μ ζ hn hU (by positivity : 0 < (K:ℝ)+1) hη1 hpos hupper hneg
    (P := fun t => mass (boundarySucc (restrictCurrent hT.1 {x | t < u x})))
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hco')
  rw [hmoment,hζ] at hs
  simpa only [Nat.cast_add,Nat.cast_ofNat] using hs

end CAT0Fillings
end

end OAI
