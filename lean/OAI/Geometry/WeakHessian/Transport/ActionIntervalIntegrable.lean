import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessianCalculus

lemma action_intervalIntegrable {a : ℝ → ℝ≥0∞}
    (ha : AEMeasurable a (volume.restrict (Icc (0 : ℝ) 1)))
    (hfin : (∫⁻ t in Icc (0 : ℝ) 1, a t) < ∞) :
    IntervalIntegrable (fun t => (a t).toReal) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr
  exact (integrable_toReal_iff ha ((ae_lt_top' ha hfin.ne).mono fun _ h => h.ne)).mpr hfin.ne

lemma action_dist_primitive {a : ℝ → ℝ≥0∞}
    (ha : AEMeasurable a (volume.restrict (Icc (0 : ℝ) 1)))
    (hfin : (∫⁻ t in Icc (0 : ℝ) 1, a t) < ∞) {q : ℝ → ℝ}
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t)
    (hqt : ENNReal.ofReal |q t - q s| ≤ ∫⁻ r in Icc s t, a r) :
    dist (q s) (q t) ≤ dist (∫ r in (0 : ℝ)..s, (a r).toReal)
      (∫ r in (0 : ℝ)..t, (a r).toReal) := by
  have hsub : Icc s t ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hs.1 ht.2
  have hstfin : (∫⁻ r in Icc s t, a r) ≠ ∞ :=
    ne_top_of_le_ne_top hfin.ne (lintegral_mono_set hsub)
  have hast : AEMeasurable a (volume.restrict (Icc s t)) :=
    ha.mono_measure (Measure.restrict_mono_set _ hsub)
  have hti := action_intervalIntegrable ha hfin
  have hi_s : IntervalIntegrable (fun r => (a r).toReal) volume 0 s :=
    hti.mono_set (by simpa only [uIcc_of_le hs.1, uIcc_of_le zero_le_one]
      using (Icc_subset_Icc le_rfl hs.2))
  have hi_t : IntervalIntegrable (fun r => (a r).toReal) volume 0 t :=
    hti.mono_set (by simpa only [uIcc_of_le ht.1, uIcc_of_le zero_le_one]
      using (Icc_subset_Icc le_rfl ht.2))
  have hreal : (∫⁻ r in Icc s t, a r).toReal = ∫ r in s..t, (a r).toReal := by
    rw [← integral_toReal hast (ae_lt_top' hast hstfin),
      integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hst]
  calc
    dist (q s) (q t) = |q t - q s| := by rw [dist_comm, Real.dist_eq]
    _ ≤ (∫⁻ r in Icc s t, a r).toReal := by
      simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using ENNReal.toReal_mono hstfin hqt
    _ = (∫ r in (0 : ℝ)..t, (a r).toReal) - ∫ r in (0 : ℝ)..s, (a r).toReal :=
      hreal.trans (intervalIntegral.integral_interval_sub_left hi_t hi_s).symm
    _ ≤ _ := by rw [dist_comm, Real.dist_eq]; exact le_abs_self _

lemma abs_deriv_le_of_dist_le {q A : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hq : DifferentiableAt ℝ q t)
    {a : ℝ} (hA : HasDerivAt A a t)
    (hdom : ∀ s ∈ Icc (0 : ℝ) 1, ∀ r ∈ Icc (0 : ℝ) 1,
      dist (q s) (q r) ≤ dist (A s) (A r)) :
    |deriv q t| ≤ |a| := by
  apply le_of_tendsto_of_tendsto hq.hasDerivAt.tendsto_slope.abs hA.tendsto_slope.abs
  have hm : ∀ᶠ s in 𝓝[≠] t, s ∈ Icc (0 : ℝ) 1 :=
    mem_of_superset (nhdsWithin_le_nhds (Ioo_mem_nhds ht.1 ht.2)) Ioo_subset_Icc_self
  filter_upwards [hm] with s hs
  simp only [slope_def_field, abs_div]
  exact div_le_div_of_nonneg_right (by simpa only [Real.dist_eq] using
    (hdom s hs t (Ioo_subset_Icc_self ht))) (abs_nonneg _)

lemma ae_deriv_le_of_dense_action {q : ℝ → ℝ} {a : ℝ → ℝ≥0∞}
    (hq : AbsolutelyContinuousOnInterval q 0 1)
    (ha : AEMeasurable a (volume.restrict (Icc (0 : ℝ) 1)))
    (hfin : (∫⁻ t in Icc (0 : ℝ) 1, a t) < ∞)
    (d : ℕ → Icc (0 : ℝ) 1) (hd : DenseRange d)
    (hbound : ∀ i j, (d i : ℝ) < d j →
      ENNReal.ofReal |q (d j) - q (d i)| ≤ ∫⁻ t in Icc (d i : ℝ) (d j : ℝ), a t) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), ENNReal.ofReal |deriv q t| ≤ a t := by
  let A : ℝ → ℝ := fun t => ∫ r in (0 : ℝ)..t, (a r).toReal
  have hi := action_intervalIntegrable ha hfin
  have hcA : Continuous (fun s : Icc (0 : ℝ) 1 => A s) := by
    apply (hi.absolutelyContinuousOnInterval_intervalIntegral (by simp)).continuousOn.comp_continuous
      continuous_subtype_val
    intro s
    simpa only [uIcc_of_le zero_le_one] using s.property
  have hcq : Continuous (fun s : Icc (0 : ℝ) 1 => q s) := by
    apply hq.continuousOn.comp_continuous continuous_subtype_val
    intro s
    simpa only [uIcc_of_le zero_le_one] using s.property
  have hdense : ∀ i j, dist (q (d i)) (q (d j)) ≤ dist (A (d i)) (A (d j)) := by
    intro i j
    rcases lt_trichotomy (d i : ℝ) (d j : ℝ) with h|h|h
    · exact action_dist_primitive ha hfin (d i).property (d j).property h.le (hbound i j h)
    · simp only [h, dist_self, le_refl]
    · simpa only [dist_comm] using
        action_dist_primitive ha hfin (d j).property (d i).property h.le (hbound j i h)
  have hall : ∀ s r : Icc (0 : ℝ) 1, dist (q s) (q r) ≤ dist (A s) (A r) := by
    intro s r
    exact (hd.prodMap hd).induction_on (p := fun z : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 =>
      dist (q z.1) (q z.2) ≤ dist (A z.1) (A z.2)) (s,r)
      (isClosed_le ((hcq.comp continuous_fst).dist (hcq.comp continuous_snd))
        ((hcA.comp continuous_fst).dist (hcA.comp continuous_snd)))
      (fun ij => hdense ij.1 ij.2)
  have haa := hi.ae_hasDerivAt_integral
  have hqa := hq.ae_differentiableAt
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_of_ae haa, ae_restrict_of_ae hqa,
    ae_restrict_mem measurableSet_Ioo] with t hAt hqt ht
  have htt : t ∈ uIcc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le zero_le_one] using Ioo_subset_Icc_self ht
  have habs := abs_deriv_le_of_dist_le ht (hqt htt)
    (hAt htt 0 (by simp)) (fun s hs r hr => hall ⟨s,hs⟩ ⟨r,hr⟩)
  calc
    ENNReal.ofReal |deriv q t| ≤ ENNReal.ofReal (a t).toReal :=
      ENNReal.ofReal_le_ofReal (by simpa only [abs_of_nonneg ENNReal.toReal_nonneg] using habs)
    _ ≤ a t := ENNReal.ofReal_toReal_le

end WeakHessianCalculus

end
end InlinedFile0

end OAI
