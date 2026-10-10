import OAI.Geometry.CylinderCovering.Nilpotent.Grid
import OAI.Geometry.RuledCovering.Main

namespace OAI

noncomputable section
open Set MeasureTheory
namespace NilpotentGrid

lemma coarseCell_volume {δ : ℝ} (hδ : 0 ≤ δ) (z : ℤ × ℤ) :
    volume.real (coarseCell δ z) = δ ^ 2 := by
  have hc := coarseCell_isCompact δ z
  rw [RuledApproximation.plane_volume_vertical_interval hc.measurableSet hc.measure_lt_top.ne
    (s := Icc (δ * (z.1 : ℝ)) (δ * ((z.1 : ℝ) + 1)))
    (l := fun _ => δ * (z.2 : ℝ)) (u := fun _ => δ * ((z.2 : ℝ) + 1))
    measurableSet_Icc (fun x => by simp only [coarseCell, mem_ofPred_eq, mem_Icc]; tauto)]
  simp only [show δ * ((z.2 : ℝ) + 1) - δ * (z.2 : ℝ) = δ by ring, max_eq_left hδ]
  rw [integral_const]
  simp only [smul_eq_mul, measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc, ENNReal.toReal_ofReal']
  rw [show δ * ((z.1 : ℝ) + 1) - δ * (z.1 : ℝ) = δ by ring, max_eq_left hδ]
  ring

lemma coordinate_zero_volume (i : Fin 2) (a : ℝ) :
    volume {x : Plane | x i = a} = 0 := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one]
  all_goals rw [← RuledApproximation.pairPlane_measurePreserving.measure_preimage_emb
    RuledApproximation.pairPlaneEquiv.measurableEmbedding]
  · have heq : RuledApproximation.pairPlaneEquiv ⁻¹' {x : Plane | x 0 = a} =
        ({a} : Set ℝ) ×ˢ (univ : Set ℝ) := by ext x; simp
    rw [heq, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  · have heq : RuledApproximation.pairPlaneEquiv ⁻¹' {x : Plane | x 1 = a} =
        (univ : Set ℝ) ×ˢ ({a} : Set ℝ) := by ext x; simp
    rw [heq, Measure.volume_eq_prod, Measure.prod_prod]
    simp

lemma unequal_cell_coordinate {δ x : ℝ} {a b : ℤ} (hδ : 0 < δ) (hab : a < b)
    (ha : x ≤ δ * ((a : ℝ) + 1)) (hb : δ * (b : ℝ) ≤ x) :
    x = δ * (b : ℝ) := by
  have hab' : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast (show a + 1 ≤ b by omega)
  have hm := mul_le_mul_of_nonneg_left hab' hδ.le
  linarith

lemma coarseCell_aeDisjoint {δ : ℝ} (hδ : 0 < δ) {z w : ℤ × ℤ} (hzw : z ≠ w) :
    AEDisjoint volume (coarseCell δ z) (coarseCell δ w) := by
  change volume (coarseCell δ z ∩ coarseCell δ w) = 0
  by_cases h0 : z.1 = w.1
  · have h1 : z.2 ≠ w.2 := by intro h; exact hzw (Prod.ext h0 h)
    rcases lt_or_gt_of_ne h1 with hlt | hlt
    · apply measure_mono_null (t := {x : Plane | x 1 = δ * (w.2 : ℝ)}) _ (coordinate_zero_volume 1 _)
      intro x hx
      exact unequal_cell_coordinate hδ hlt hx.1.2.2.2 hx.2.2.2.1
    · apply measure_mono_null (t := {x : Plane | x 1 = δ * (z.2 : ℝ)}) _ (coordinate_zero_volume 1 _)
      intro x hx
      exact unequal_cell_coordinate hδ hlt hx.2.2.2.2 hx.1.2.2.1
  · rcases lt_or_gt_of_ne h0 with hlt | hlt
    · apply measure_mono_null (t := {x : Plane | x 0 = δ * (w.1 : ℝ)}) _ (coordinate_zero_volume 0 _)
      intro x hx
      exact unequal_cell_coordinate hδ hlt hx.1.2.1 hx.2.1
    · apply measure_mono_null (t := {x : Plane | x 0 = δ * (z.1 : ℝ)}) _ (coordinate_zero_volume 0 _)
      intro x hx
      exact unequal_cell_coordinate hδ hlt hx.2.2.1 hx.1.1

lemma coarseUnion_volume {δ B : ℝ} (hδ : 0 < δ) (D : Set Plane) :
    volume.real (coarseUnion δ B D) = ((coarseIndices δ B D).card : ℝ) * δ ^ 2 := by
  classical
  rw [coarseUnion, measureReal_biUnion_finset₀
    (fun _ _ _ _ hne => coarseCell_aeDisjoint hδ hne)
    (fun z _ => (coarseCell_isCompact δ z).measurableSet.nullMeasurableSet)
    (fun z _ => (coarseCell_isCompact δ z).measure_lt_top.ne)]
  simp only [coarseCell_volume hδ.le, Finset.sum_const, nsmul_eq_mul]

lemma coarseUnion_integral {δ B : ℝ} (hδ : 0 < δ) (D : Set Plane)
    (f : Plane → ℝ) (hf : IntegrableOn f (coarseUnion δ B D)) :
    ∫ x in coarseUnion δ B D, f x =
      ∑ z ∈ coarseIndices δ B D, ∫ x in coarseCell δ z, f x := by
  classical
  let S := coarseIndices δ B D
  have heq : coarseUnion δ B D = ⋃ z : S, coarseCell δ z.1 := by
    ext x
    simp [coarseUnion, S]
  rw [heq]
  rw [integral_iUnion_ae
    (fun z : S => (coarseCell_isCompact δ z.1).measurableSet.nullMeasurableSet)
    (fun z w hne => coarseCell_aeDisjoint hδ (fun h => hne (Subtype.ext h)))]
  · rw [tsum_fintype]
    exact Finset.sum_coe_sort S (fun z => ∫ x in coarseCell δ z, f x)
  · rw [← heq]
    exact hf

lemma coarseCell_integral_error {δ L : ℝ} {z : ℤ × ℤ} {b : Plane}
    (hδ : 0 ≤ δ) (hL : 0 ≤ L) (hb : b ∈ coarseCell δ z)
    (f : Plane → ℝ) (hf : IntegrableOn f (coarseCell δ z))
    (hLip : ∀ x ∈ coarseCell δ z, |f x - f b| ≤ L * ‖x - b‖) :
    |(∫ x in coarseCell δ z, f x) - δ ^ 2 * f b| ≤
      L * Real.sqrt 2 * δ ^ 3 := by
  have hc := coarseCell_isCompact δ z
  have hconst : IntegrableOn (fun _ : Plane => f b) (coarseCell δ z) :=
    continuousOn_const.integrableOn_compact hc
  have heq : (∫ x in coarseCell δ z, f x) - δ ^ 2 * f b =
      ∫ x in coarseCell δ z, (f x - f b) := by
    rw [integral_sub hf hconst, integral_const]
    simp only [smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
    rw [← measureReal_def, coarseCell_volume hδ]
  rw [heq, ← Real.norm_eq_abs]
  calc
    ‖∫ x in coarseCell δ z, (f x - f b)‖ ≤
        (L * (Real.sqrt 2 * δ)) * volume.real (coarseCell δ z) := by
      apply norm_setIntegral_le_of_norm_le_const hc.measure_lt_top
      intro x hx
      rw [Real.norm_eq_abs]
      exact (hLip x hx).trans (mul_le_mul_of_nonneg_left (same_cell_distance hδ hx hb) hL)
    _ = L * Real.sqrt 2 * δ ^ 3 := by rw [coarseCell_volume hδ]; ring

theorem coarseUnion_integral_error {δ B L : ℝ} (D : Set Plane)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (b : ℤ × ℤ → Plane) (hb : ∀ z ∈ coarseIndices δ B D, b z ∈ coarseCell δ z)
    (f : Plane → ℝ) (hf : IntegrableOn f (coarseUnion δ B D))
    (hLip : ∀ z ∈ coarseIndices δ B D, ∀ x ∈ coarseCell δ z,
      |f x - f (b z)| ≤ L * ‖x - b z‖) :
    |(∫ x in coarseUnion δ B D, f x) -
      ∑ z ∈ coarseIndices δ B D, δ ^ 2 * f (b z)| ≤
      (2 * B + 4) ^ 2 * L * Real.sqrt 2 * δ := by
  classical
  let S := coarseIndices δ B D
  have hcell (z : ℤ × ℤ) (hz : z ∈ S) :
      |(∫ x in coarseCell δ z, f x) - δ ^ 2 * f (b z)| ≤ L * Real.sqrt 2 * δ ^ 3 := by
    apply coarseCell_integral_error hδ.le hL (hb z hz) f
    · apply hf.mono_set
      exact subset_iUnion₂_of_subset z hz subset_rfl
    · exact hLip z hz
  rw [coarseUnion_integral hδ D f hf, ← Finset.sum_sub_distrib]
  have hsum := (Finset.abs_sum_le_sum_abs
    (fun z => (∫ x in coarseCell δ z, f x) - δ ^ 2 * f (b z)) S).trans
      (Finset.sum_le_sum hcell)
  have hcount := mul_le_mul_of_nonneg_right (coarse_count_bound D hδ hδ1 hB)
    (show 0 ≤ L * Real.sqrt 2 * δ by positivity)
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  dsimp [S] at hsum
  nlinarith only [hsum, hcount]

lemma coarseUnion_integral_le {δ B : ℝ} {D : Set Plane}
    (hδ : 0 < δ) (hD : MeasurableSet D)
    (hbound : ∀ x ∈ D, |x 0| ≤ B ∧ |x 1| ≤ B)
    (f : Plane → ℝ) (hf : IntegrableOn f (coarseUnion δ B D))
    (hf1 : ∀ x ∈ coarseUnion δ B D \ D, f x ≤ 1) :
    (∫ x in coarseUnion δ B D, f x) ≤
      (∫ x in D, f x) + volume.real (coarseUnion δ B D \ D) := by
  have hsub := subset_coarseUnion hδ hbound
  have hu := coarseUnion_isCompact δ B D
  have hdiff := hu.measurableSet.diff hD
  have hfinite : volume (coarseUnion δ B D \ D) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono sdiff_subset) hu.measure_lt_top).ne
  have hle := setIntegral_mono_on (hf.mono_set sdiff_subset)
    (integrableOn_const hfinite : IntegrableOn (fun _ : Plane => (1 : ℝ))
      (coarseUnion δ B D \ D)) hdiff hf1
  rw [setIntegral_const, smul_eq_mul, mul_one, setIntegral_sdiff hD hf hsub] at hle
  linarith only [hle]

theorem tagged_sum_le_domain_integral {δ B L : ℝ} {D : Set Plane}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hD : MeasurableSet D) (hbound : ∀ x ∈ D, |x 0| ≤ B ∧ |x 1| ≤ B)
    (b : ℤ × ℤ → Plane) (hb : ∀ z ∈ coarseIndices δ B D, b z ∈ coarseCell δ z)
    (f : Plane → ℝ) (hf : IntegrableOn f (coarseUnion δ B D))
    (hf1 : ∀ x ∈ coarseUnion δ B D \ D, f x ≤ 1)
    (hLip : ∀ z ∈ coarseIndices δ B D, ∀ x ∈ coarseCell δ z,
      |f x - f (b z)| ≤ L * ‖x - b z‖) :
    (∑ z ∈ coarseIndices δ B D, δ ^ 2 * f (b z)) ≤
      (∫ x in D, f x) + (2 * B + 4) ^ 2 * L * Real.sqrt 2 * δ +
        volume.real (coarseUnion δ B D \ D) := by
  have herror := coarseUnion_integral_error D hδ hδ1 hB hL b hb f hf hLip
  have hupper := coarseUnion_integral_le hδ hD hbound f hf hf1
  have herr := (abs_le.mp herror).1
  linarith only [herr, hupper]

lemma coarseCell_integral_error_of_oscillation {δ W : ℝ} {z : ℤ × ℤ} {b : Plane}
    (hδ : 0 ≤ δ) (f : Plane → ℝ) (hf : IntegrableOn f (coarseCell δ z))
    (hosc : ∀ x ∈ coarseCell δ z, |f x - f b| ≤ W * δ) :
    |(∫ x in coarseCell δ z, f x) - δ ^ 2 * f b| ≤ W * δ ^ 3 := by
  have hc := coarseCell_isCompact δ z
  have hconst : IntegrableOn (fun _ : Plane => f b) (coarseCell δ z) :=
    continuousOn_const.integrableOn_compact hc
  have heq : (∫ x in coarseCell δ z, f x) - δ ^ 2 * f b =
      ∫ x in coarseCell δ z, (f x - f b) := by
    rw [integral_sub hf hconst, integral_const]
    simp only [smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
    rw [← measureReal_def, coarseCell_volume hδ]
  rw [heq, ← Real.norm_eq_abs]
  calc
    ‖∫ x in coarseCell δ z, (f x - f b)‖ ≤
        (W * δ) * volume.real (coarseCell δ z) := by
      apply norm_setIntegral_le_of_norm_le_const hc.measure_lt_top
      intro x hx
      simpa only [Real.norm_eq_abs] using hosc x hx
    _ = W * δ ^ 3 := by rw [coarseCell_volume hδ]; ring

theorem coarseUnion_integral_error_of_oscillation {δ B W : ℝ} (D : Set Plane)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hB : 0 ≤ B) (hW : 0 ≤ W)
    (b : ℤ × ℤ → Plane) (f : Plane → ℝ)
    (hf : IntegrableOn f (coarseUnion δ B D))
    (hosc : ∀ z ∈ coarseIndices δ B D, ∀ x ∈ coarseCell δ z,
      |f x - f (b z)| ≤ W * δ) :
    |(∫ x in coarseUnion δ B D, f x) -
      ∑ z ∈ coarseIndices δ B D, δ ^ 2 * f (b z)| ≤ (2 * B + 4) ^ 2 * W * δ := by
  classical
  let S := coarseIndices δ B D
  have hcell (z : ℤ × ℤ) (hz : z ∈ S) :
      |(∫ x in coarseCell δ z, f x) - δ ^ 2 * f (b z)| ≤ W * δ ^ 3 := by
    apply coarseCell_integral_error_of_oscillation hδ.le f
    · apply hf.mono_set
      exact subset_iUnion₂_of_subset z hz subset_rfl
    · exact hosc z hz
  rw [coarseUnion_integral hδ D f hf, ← Finset.sum_sub_distrib]
  have hsum := (Finset.abs_sum_le_sum_abs
    (fun z => (∫ x in coarseCell δ z, f x) - δ ^ 2 * f (b z)) S).trans
      (Finset.sum_le_sum hcell)
  have hcount := mul_le_mul_of_nonneg_right (coarse_count_bound D hδ hδ1 hB)
    (mul_nonneg hW hδ.le)
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  dsimp [S] at hsum
  nlinarith only [hsum, hcount]

theorem tagged_sum_le_domain_integral_of_oscillation {δ B W : ℝ} {D : Set Plane}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hB : 0 ≤ B) (hW : 0 ≤ W)
    (hD : MeasurableSet D) (hbound : ∀ x ∈ D, |x 0| ≤ B ∧ |x 1| ≤ B)
    (b : ℤ × ℤ → Plane) (f : Plane → ℝ)
    (hf : IntegrableOn f (coarseUnion δ B D))
    (hf1 : ∀ x ∈ coarseUnion δ B D \ D, f x ≤ 1)
    (hosc : ∀ z ∈ coarseIndices δ B D, ∀ x ∈ coarseCell δ z,
      |f x - f (b z)| ≤ W * δ) :
    (∑ z ∈ coarseIndices δ B D, δ ^ 2 * f (b z)) ≤
      (∫ x in D, f x) + (2 * B + 4) ^ 2 * W * δ +
        volume.real (coarseUnion δ B D \ D) := by
  have herror := coarseUnion_integral_error_of_oscillation D hδ hδ1 hB hW b f hf hosc
  have hupper := coarseUnion_integral_le hδ hD hbound f hf hf1
  have herr := (abs_le.mp herror).1
  linarith only [herr, hupper]

end NilpotentGrid

end

end OAI
