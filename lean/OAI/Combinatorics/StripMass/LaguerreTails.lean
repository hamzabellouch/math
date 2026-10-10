import Mathlib
import OAI.Combinatorics.StripMass.TailIntegrals

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory
theorem laguerreLaw_small_coordinate_le {N : ℕ} {a h : ℝ}
    (ha : 0 < a) (hh : 0 < h) (i : Fin N) :
    (laguerreLaw N a).real {r | r i < h} ≤
      min 1 (laguerreSmallCoefficient N a (i.val + 1) *
        h ^ laguerreDimension a (i.val + 1)) := by
  let := laguerreLaw_isProbabilityMeasure N ha
  refine le_min (measureReal_le_one (μ := laguerreLaw N a)) ?_
  have H := laguerreLaw_small_coordinate_le_normalizer_ratio ha hh i
  apply H.trans_eq
  simp only [laguerreSmallCoefficient, Nat.cast_add, Nat.cast_one]
  ring

theorem laguerreLaw_small_coordinate_power_bound {N : ℕ} {a h : ℝ}
    (ha : 0 < a) (hh : 0 < h) (i : Fin N) :
    (laguerreLaw N a).real {r | r i < h} ≤
      (laguerreSmallCoefficient N a (i.val + 1) ^
        (1 / laguerreDimension a (i.val + 1)) * h) ^ laguerreDimension a (i.val + 1) := by
  have hb := laguerreSmallCoefficient_pos N (i.val + 1) ha
  have hD := laguerreDimension_pos ha (show 1 ≤ i.val + 1 by omega)
  have H := (laguerreLaw_small_coordinate_le ha hh i).trans (min_le_right _ _)
  rw [Real.mul_rpow (Real.rpow_pos_of_pos hb _).le hh.le,
    ← Real.rpow_mul hb.le, one_div_mul_cancel hD.ne', Real.rpow_one]
  exact H

 

theorem integrable_inverse_of_small_tail {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {X : α → ℝ}
    (hX : ∀ᵐ x ∂μ, 0 < X x) {A D p : ℝ} (hA : 0 < A) (hp : 0 < p)
    (hpD : p < D) (hXm : AEMeasurable X μ)
    (htail : ∀ h > 0, μ.real {x | X x < h} ≤ (A * h) ^ D) :
    Integrable (fun x => (X x) ^ (-p)) μ := by
  have hq : 1 < D / p := (lt_div_iff₀ hp).2 (by simpa using hpD)
  have hnn : 0 ≤ᵐ[μ] (fun x => (X x) ^ (-p)) := by
    filter_upwards [hX] with x hx
    exact (Real.rpow_pos_of_pos hx _).le
  apply integrable_of_power_tail (hXm.pow_const _) hnn (Real.rpow_pos_of_pos hA p) hq
  intro t ht
  have htpos : 0 < t := (Real.rpow_pos_of_pos hA p).trans ht
  have htpow : 0 < t ^ (-1 / p) := Real.rpow_pos_of_pos htpos _
  have hsets : {x | t < (X x) ^ (-p)} =ᵐ[μ] {x | X x < t ^ (-1 / p)} := by
    filter_upwards [hX] with x hx
    have hh := Real.rpow_lt_rpow_iff_of_neg htpow hx (by linarith : -p < 0)
    rw [← Real.rpow_mul htpos.le, show (-1 / p) * -p = (1 : ℝ) by field_simp, Real.rpow_one] at hh
    exact propext hh
  have hmeas : μ.real {x | t < (X x) ^ (-p)} = μ.real {x | X x < t ^ (-1 / p)} :=
    congrArg ENNReal.toReal (measure_congr hsets)
  rw [hmeas]
  calc
    _ ≤ (A * t ^ (-1 / p)) ^ D := htail _ htpow
    _ = (A ^ p) ^ (D / p) * t ^ (-(D / p)) := by
      rw [Real.mul_rpow hA.le htpow.le, ← Real.rpow_mul htpos.le, ← Real.rpow_mul hA.le,
        show p * (D / p) = D by field_simp,
        show (-1 / p) * D = -(D / p) by ring]

 
theorem integrable_laguerreLaw_inverse_coordinate_full {N : ℕ} {a p : ℝ}
    (ha : 0 < a) (i : Fin N) (hpD : p < laguerreDimension a (i.val + 1)) :
    Integrable (fun r => (r i) ^ (-p)) (laguerreLaw N a) := by
  by_cases hp : 0 < p
  · let := laguerreLaw_isProbabilityMeasure N ha
    apply integrable_inverse_of_small_tail (D := laguerreDimension a (i.val + 1))
      (A := laguerreSmallCoefficient N a (i.val + 1) ^ (1 / laguerreDimension a (i.val + 1)))
      ?_ (Real.rpow_pos_of_pos (laguerreSmallCoefficient_pos _ _ ha) _) hp hpD
      (measurable_pi_apply i).aemeasurable
      (fun h hh => laguerreLaw_small_coordinate_power_bound ha hh i)
    filter_upwards [ae_laguerreDomain N a] with r hr
    exact hr.2 i
  · apply integrable_laguerreLaw_inverse_coordinate ha i
    have hi : (0 : ℝ) ≤ i.val := by positivity
    linarith

 

theorem laguerre_inverse_bound_normalizer_ratio {N : ℕ} {a p : ℝ}
    (ha : 0 < a) (i : Fin N) (hp : 0 < p)
    (hpD : p < laguerreDimension a (i.val + 1)) :
    laguerreExpectation N a (fun r => (r i) ^ (-p)) ≤
      laguerreDimension a (i.val + 1) / (laguerreDimension a (i.val + 1) - p) *
        laguerreSmallCoefficient N a (i.val + 1) ^ (p / laguerreDimension a (i.val + 1)) := by
  let := laguerreLaw_isProbabilityMeasure N ha
  rw [← integral_laguerreLaw N ha]
  have hX : ∀ᵐ r ∂laguerreLaw N a, 0 < r i := by
    filter_upwards [ae_laguerreDomain N a] with r hr
    exact hr.2 i
  have hb := laguerreSmallCoefficient_pos N (i.val + 1) ha
  have H := integral_inverse_le_of_small_tail hX
    (Real.rpow_pos_of_pos hb (1 / laguerreDimension a (i.val + 1))) hp hpD
    (measurable_pi_apply i).aemeasurable
    (fun h hh => laguerreLaw_small_coordinate_power_bound ha hh i)
  simpa only [← Real.rpow_mul hb.le, one_div_mul_eq_div] using H


 


theorem pairProduct_snoc {n : ℕ} (x : ℝ) (r : Fin n → ℝ) :
    (∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i,
      pairKernel ((Fin.snoc r x : Fin (n + 1) → ℝ) i) ((Fin.snoc r x : Fin (n + 1) → ℝ) j)) =
      (∏ i, ∏ j ∈ Finset.Ioi i, pairKernel (r i) (r j)) * ∏ i, pairKernel (r i) x := by
  classical
  have he {m : ℕ} (s : Fin m → ℝ) :
      (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, pairKernel (s i) (s j)) =
        ∏ i : Fin m, ∏ j : Fin m, if i < j then pairKernel (s i) (s j) else 1 := by
    apply Finset.prod_congr rfl
    intro i _
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp
  rw [he, he]
  simp [Fin.prod_univ_castSucc, Finset.prod_mul_distrib, not_lt.mpr (Fin.le_last _)]

theorem laguerreDensity_snoc {n : ℕ} (a x : ℝ) (r : Fin n → ℝ) :
    laguerreDensity (n + 1) a (Fin.snoc r x) =
      laguerreWeight a x * laguerreDensity n a r * ∏ i, pairKernel (r i) x := by
  unfold laguerreDensity
  rw [pairProduct_snoc]
  simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  ring

theorem laguerreDomain_of_snoc {n : ℕ} {x : ℝ} {r : Fin n → ℝ}
    (hr : Fin.snoc r x ∈ laguerreDomain (n + 1)) :
    r ∈ laguerreDomain n ∧ 0 < x ∧ ∀ i, r i < x := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro i j hij
    simpa using hr.1 (show i.castSucc < j.castSucc from hij)
  · intro i
    simpa using hr.2 i.castSucc
  · simpa using hr.2 (Fin.last n)
  · intro i
    simpa using hr.1 (Fin.castSucc_lt_last i)

theorem laguerreDensity_snoc_le {n : ℕ} (a : ℝ) {x : ℝ} {r : Fin n → ℝ}
    (hr : Fin.snoc r x ∈ laguerreDomain (n + 1)) :
    laguerreDensity (n + 1) a (Fin.snoc r x) ≤
      laguerreWeight (a + n) x * laguerreDensity n a r := by
  obtain ⟨hrt, hx, hrx⟩ := laguerreDomain_of_snoc hr
  rw [laguerreDensity_snoc]
  have hp : (∏ i, pairKernel (r i) x) ≤ x ^ n := by
    calc
      _ ≤ ∏ _ : Fin n, x := Finset.prod_le_prod₀
        (fun i _ => pairKernel_nonneg (hrt.2 i).le hx.le)
        (fun i _ => pairKernel_le_right (hrt.2 i).le hx (hrx i).le)
      _ = _ := by simp
  calc
    _ ≤ (laguerreWeight a x * laguerreDensity n a r) * x ^ n :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg (laguerreWeight_pos a hx).le (laguerreDensity_pos a hrt).le)
    _ = laguerreWeight (a + n) x * laguerreDensity n a r := by
      unfold laguerreWeight
      rw [show a + (n : ℝ) - 1 = a - 1 + n by ring, Real.rpow_add hx, Real.rpow_natCast]
      ring

theorem integral_fin_snoc_eq (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ) :
    (∫ r, f r) = ∫ p : ℝ × (Fin n → ℝ), f (Fin.snoc p.2 p.1) := by
  symm
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_last, Fin.succAbove_last, Equiv.coe_fn_mk, cast_eq] using
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm).integral_comp' f

theorem integrable_fin_snoc {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : Integrable f) : Integrable (fun p : ℝ × (Fin n → ℝ) => f (Fin.snoc p.2 p.1)) := by
  simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_last, Fin.succAbove_last, Equiv.coe_fn_mk, cast_eq] using
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm).integrable_comp_of_integrable hf

theorem laguerreLaw_measureReal (N : ℕ) {a : ℝ} (ha : 0 < a)
    {s : Set (Fin N → ℝ)} (hs : MeasurableSet s) :
    (laguerreLaw N a).real s =
      (∫ r in laguerreDomain N ∩ s, laguerreDensity N a r) / laguerreNormalizer N a := by
  rw [← integral_indicator_one hs, integral_laguerreLaw N ha]
  unfold laguerreExpectation
  simp_rw [← Set.indicator_mul_left, Pi.one_apply, one_mul]
  rw [setIntegral_indicator hs]

theorem laguerreLargestIntegral_le (n : ℕ) {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h) :
    (∫ r in laguerreDomain (n + 1) ∩ {r | h < r (Fin.last n)}, laguerreDensity (n + 1) a r) ≤
      (∫ x in Ioi h, laguerreWeight (a + n) x) * laguerreNormalizer n a := by
  let S : Set (Fin (n + 1) → ℝ) := laguerreDomain (n + 1) ∩ {r | h < r (Fin.last n)}
  have hm : MeasurableSet S := (isOpen_laguerreDomain _).measurableSet.inter
    (measurableSet_lt measurable_const (measurable_pi_apply _))
  let f : ℝ → ℝ := (Ioi h).indicator (laguerreWeight (a + n))
  let g : (Fin n → ℝ) → ℝ := (laguerreDomain n).indicator (laguerreDensity n a)
  have hfi : Integrable f := (integrable_indicator_iff measurableSet_Ioi).2
    ((integrableOn_laguerreWeight (show 0 < a + (n : ℝ) by positivity)).mono_set (Ioi_subset_Ioi hh))
  have hgi : Integrable g := (integrable_indicator_iff (isOpen_laguerreDomain n).measurableSet).2
    (integrableOn_laguerreDensity n ha)
  have hfn : ∀ x, 0 ≤ f x := by
    intro x
    by_cases hx : h < x
    · rw [show f x = laguerreWeight (a + n) x from indicator_of_mem hx _]
      exact (laguerreWeight_pos _ (hh.trans_lt hx)).le
    · exact le_of_eq (indicator_of_notMem hx _).symm
  have hgn : ∀ r, 0 ≤ g r := by
    intro r
    by_cases hr : r ∈ laguerreDomain n
    · rw [show g r = laguerreDensity n a r from indicator_of_mem hr _]
      exact (laguerreDensity_pos a hr).le
    · exact le_of_eq (indicator_of_notMem hr _).symm
  have hsi : Integrable (S.indicator (laguerreDensity (n + 1) a)) :=
    (integrable_indicator_iff hm).2 ((integrableOn_laguerreDensity _ ha).mono_set inter_subset_left)
  have hb (p : ℝ × (Fin n → ℝ)) : S.indicator (laguerreDensity (n + 1) a) (Fin.snoc p.2 p.1) ≤
      f p.1 * g p.2 := by
    by_cases hp : Fin.snoc p.2 p.1 ∈ S
    · have htail := (laguerreDomain_of_snoc hp.1).1
      have hx : p.1 ∈ Ioi h := by simpa using hp.2
      simpa only [f, g, indicator_of_mem hp, indicator_of_mem hx, indicator_of_mem htail] using
        laguerreDensity_snoc_le a hp.1
    · rw [indicator_of_notMem hp]
      exact mul_nonneg (hfn _) (hgn _)
  calc
    _ = ∫ p : ℝ × (Fin n → ℝ), S.indicator (laguerreDensity (n + 1) a) (Fin.snoc p.2 p.1) := by
      rw [← integral_indicator hm, integral_fin_snoc_eq]
    _ ≤ ∫ p : ℝ × (Fin n → ℝ), f p.1 * g p.2 :=
      integral_mono (integrable_fin_snoc hsi) (hfi.mul_prod hgi) hb
    _ = (∫ x, f x) * ∫ r, g r := integral_prod_mul f g
    _ = _ := by
      simp only [f, g, integral_indicator measurableSet_Ioi,
        integral_indicator (isOpen_laguerreDomain n).measurableSet, laguerreNormalizer]

 
theorem laguerreLaw_max_tail_le (n : ℕ) {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h) :
    (laguerreLaw (n + 1) a).real {r | h < r (Fin.last n)} ≤
      (laguerreNormalizer n a / laguerreNormalizer (n + 1) a) *
        ∫ x in Ioi h, laguerreWeight (a + n) x := by
  rw [laguerreLaw_measureReal _ ha (measurableSet_lt measurable_const (measurable_pi_apply _))]
  have H := div_le_div_of_nonneg_right (laguerreLargestIntegral_le n ha hh)
    (laguerreNormalizer_pos (n + 1) ha).le
  exact H.trans_eq (by ring)

 

theorem laguerreWeight_tail_exp_bound {b h : ℝ} (hb : 0 < b) (hh : 0 ≤ h) :
    (∫ x in Ioi h, laguerreWeight b x) ≤
      Real.exp (-h / 2) * (2 ^ b * Real.Gamma b) := by
  let f : ℝ → ℝ := fun x => x ^ (b - 1) * Real.exp (-(1 / 2 * x))
  have hfi : IntegrableOn f (Ioi 0) := by
    simpa only [f, Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := b - 1) (p := 1) (b := 1 / 2)
        (by linarith) (by norm_num) (by norm_num))
  have hfn : ∀ x ∈ Ioi 0, 0 ≤ f x := fun x hx =>
    mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (Real.exp_nonneg _)
  have ht : ∫ x in Ioi h, laguerreWeight b x ≤ Real.exp (-h / 2) * ∫ x in Ioi h, f x := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on
      ((integrableOn_laguerreWeight hb).mono_set (Ioi_subset_Ioi hh))
      ((hfi.mono_set (Ioi_subset_Ioi hh)).const_mul _) measurableSet_Ioi
    intro x hx
    have hxpos : 0 < x := lt_of_le_of_lt hh hx
    have he : Real.exp (-x / 2) ≤ Real.exp (-h / 2) :=
      Real.exp_le_exp.2 (by have : h < x := hx; linarith)
    calc
      laguerreWeight b x = Real.exp (-x / 2) * f x := by
        simp only [laguerreWeight, f]
        conv_lhs => rw [show -x = -(x / 2) + -(1 / 2 * x) by ring, Real.exp_add]
        simp only [neg_div, mul_left_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_right he (hfn x hxpos)
  calc
    _ ≤ Real.exp (-h / 2) * ∫ x in Ioi h, f x := ht
    _ ≤ Real.exp (-h / 2) * ∫ x in Ioi 0, f x := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      apply setIntegral_mono_set hfi _ (Filter.Eventually.of_forall (Ioi_subset_Ioi hh))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hfn x hx
    _ = _ := by
      congr 1
      simpa only [f, one_div_div, div_one] using
        (Real.integral_rpow_mul_exp_neg_mul_Ioi hb (by norm_num : (0 : ℝ) < 1 / 2))

 

theorem laguerreLaw_max_tail_exp_bound (n : ℕ) {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h) :
    (laguerreLaw (n + 1) a).real {r | h < r (Fin.last n)} ≤
      (laguerreNormalizer n a / laguerreNormalizer (n + 1) a) *
        (Real.exp (-h / 2) * (2 ^ (a + (n : ℝ)) * Real.Gamma (a + n))) := by
  apply (laguerreLaw_max_tail_le n ha hh).trans
  exact mul_le_mul_of_nonneg_left
    (laguerreWeight_tail_exp_bound (by positivity) hh)
    (div_nonneg (laguerreNormalizer_pos n ha).le (laguerreNormalizer_pos (n + 1) ha).le)

end

noncomputable section
open scoped BigOperators
open Set MeasureTheory Filter

 
def orderedPairKernel (x y : ℝ) : ℝ := (max (y - x) 0) ^ 2 / (y + x)

lemma orderedPairKernel_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ orderedPairKernel x y := by
  unfold orderedPairKernel
  positivity

lemma orderedPairKernel_eq {x y : ℝ} (hxy : x ≤ y) :
    orderedPairKernel x y = pairKernel x y := by
  simp [orderedPairKernel, pairKernel, max_eq_left (sub_nonneg.mpr hxy)]

lemma orderedPairKernel_eq_zero {x y : ℝ} (hxy : y ≤ x) :
    orderedPairKernel x y = 0 := by
  simp [orderedPairKernel, max_eq_right (sub_nonpos.mpr hxy)]

 

lemma pairKernel_cross {a b s t : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbs : b < s) (hst : s ≤ t) :
    pairKernel a t * pairKernel b s ≤ pairKernel a s * pairKernel b t := by
  have hb : 0 < b := ha.trans_le hab
  have has : a < s := hab.trans_lt hbs
  have hat : a < t := has.trans_le hst
  have hbt : b < t := hbs.trans_le hst
  have hu : (s - b) / (t - b) ≤ (s - a) / (t - a) := by
    rw [div_le_div_iff₀ (sub_pos.mpr hbt) (sub_pos.mpr hat)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hst)]
  have hv : (t + b) / (s + b) ≤ (t + a) / (s + a) := by
    rw [div_le_div_iff₀ (by linarith : 0 < s + b) (by linarith : 0 < s + a)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hst)]
  have hr : pairKernel b s / pairKernel b t ≤ pairKernel a s / pairKernel a t := by
    have he {u : ℝ} (hu0 : 0 < u) (hus : u < s) :
        pairKernel u s / pairKernel u t = ((s - u) / (t - u)) ^ 2 * ((t + u) / (s + u)) := by
      unfold pairKernel
      field_simp
    rw [he hb hbs, he ha has]
    refine mul_le_mul ((sq_le_sq₀ (by positivity) (by positivity)).2 hu) hv ?_ (sq_nonneg _)
    exact div_nonneg (by linarith) (by linarith)
  have hr' := (div_le_div_iff₀ (pairKernel_pos hb hbt) (pairKernel_pos ha hat)).1 hr
  nlinarith

lemma orderedPairKernel_logSupermodular {a b s t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) (ht : 0 < t) :
    orderedPairKernel a s * orderedPairKernel b t ≤
      orderedPairKernel (min a b) (min s t) * orderedPairKernel (max a b) (max s t) := by
  wlog hab : a ≤ b generalizing a b s t
  · have h := this hb ha ht hs (le_of_not_ge hab)
    simpa [min_comm, max_comm, mul_comm] using h
  by_cases hst : s ≤ t
  · simp [min_eq_left hab, max_eq_right hab, min_eq_left hst, max_eq_right hst]
  have hts : t ≤ s := le_of_not_ge hst
  rw [min_eq_left hab, max_eq_right hab, min_eq_right hts, max_eq_left hts]
  by_cases hbt : b < t
  · rw [orderedPairKernel_eq (hab.trans (hbt.le.trans hts)), orderedPairKernel_eq hbt.le,
      orderedPairKernel_eq (hab.trans hbt.le), orderedPairKernel_eq (hbt.le.trans hts)]
    exact pairKernel_cross ha hab hbt hts
  · rw [orderedPairKernel_eq_zero (le_of_not_gt hbt), mul_zero]
    exact mul_nonneg (orderedPairKernel_nonneg ha.le ht.le)
      (orderedPairKernel_nonneg hb.le hs.le)

 

lemma product_coordinate_modular {ι α : Type*} [Fintype ι] [LinearOrder α]
    (w : ι → α → ℝ) (x y : ι → α) :
    (∏ i, w i (x i)) * (∏ i, w i (y i)) =
      (∏ i, w i ((x ⊓ y) i)) * (∏ i, w i ((x ⊔ y) i)) := by
  classical
  simp only [← Finset.prod_mul_distrib, Pi.inf_apply, Pi.sup_apply]
  apply Finset.prod_congr rfl
  intro i _
  obtain h | h := le_total (x i) (y i)
  · simp [inf_eq_left.mpr h, sup_eq_right.mpr h]
  · simp [inf_eq_right.mpr h, sup_eq_left.mpr h, mul_comm]

 

lemma association_finite_product {ι α : Type*} [Fintype ι] [Fintype α] [LinearOrder α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : ι → Measure α) [∀ i, IsFiniteMeasure (ν i)]
    (h f g : (ι → α) → ℝ) (hh : 0 ≤ h) (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hfm : Monotone f) (hgm : Monotone g)
    (hhm : ∀ x y, h x * h y ≤ h (x ⊓ y) * h (x ⊔ y)) :
    (∫ x, h x * f x ∂Measure.pi ν) * (∫ x, h x * g x ∂Measure.pi ν) ≤
      (∫ x, h x ∂Measure.pi ν) * (∫ x, h x * (f x * g x) ∂Measure.pi ν) := by
  classical
  let m : (ι → α) → ℝ := fun x => ∏ i, (ν i).real {x i}
  have hm : ∀ x, (Measure.pi ν).real {x} = m x := by
    intro x
    simp only [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod, m]
  have hmn : 0 ≤ m := fun x => Finset.prod_nonneg fun i _ => measureReal_nonneg
  have hmod (x y : ι → α) : m x * m y = m (x ⊓ y) * m (x ⊔ y) :=
    product_coordinate_modular (fun i z => (ν i).real {z}) x y
  have hmh : ∀ x y, (m x * h x) * (m y * h y) ≤
      (m (x ⊓ y) * h (x ⊓ y)) * (m (x ⊔ y) * h (x ⊔ y)) := by
    intro x y
    rw [mul_mul_mul_comm, mul_mul_mul_comm (m (x ⊓ y)), hmod]
    exact mul_le_mul_of_nonneg_left (hhm x y) (mul_nonneg (hmn _) (hmn _))
  simp only [integral_fintype (Integrable.of_finite), hm, smul_eq_mul]
  simpa only [mul_assoc] using
    fkg f g (fun x => m x * h x) (fun x => mul_nonneg (hmn x) (hh x))
      hf hg hfm hgm hmh

def coordinateBox (ι : Type*) (I : Set ℝ) : Set (ι → ℝ) := {x | ∀ i, x i ∈ I}

 

end
end CriticalStrip

end OAI
