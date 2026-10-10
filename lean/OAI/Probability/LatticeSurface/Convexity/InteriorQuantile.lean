import Mathlib

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace SliceTransport

def cumulative (f : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  (∫ t in a..x, f t) / (∫ t in a..b, f t)

def quantile (f : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ :=
  Function.invFunOn (cumulative f a b) (Icc a b)

structure IntervalDensity (f : ℝ → ℝ) (a b : ℝ) : Prop where
  integrable : IntervalIntegrable f volume a b
  continuous : ContinuousOn f (Ioo a b)

lemma IntervalDensity.continuousAt {f : ℝ → ℝ} {a b x : ℝ}
    (hf : IntervalDensity f a b) (hx : x ∈ Ioo a b) : ContinuousAt f x :=
  (hf.continuous x hx).continuousAt (isOpen_Ioo.mem_nhds hx)

lemma integral_positive {f : ℝ → ℝ} {a b : ℝ} (hf : IntervalDensity f a b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) (hab : a < b) : 0 < ∫ t in a..b, f t :=
  intervalIntegral.intervalIntegral_pos_of_pos_on hf.integrable hpos hab

lemma cumulative_hasDerivAt {f : ℝ → ℝ} {a b x : ℝ} (hf : IntervalDensity f a b)
    (hx : x ∈ Ioo a b) :
    HasDerivAt (cumulative f a b) (f x / (∫ t in a..b, f t)) x := by
  have hi : IntervalIntegrable f volume a x := by
    apply hf.integrable.mono_set
    rw [uIcc_of_le hx.1.le, uIcc_of_le (hx.1.trans hx.2).le]
    exact Icc_subset_Icc_right hx.2.le
  exact (intervalIntegral.integral_hasDerivAt_right hi
    (hf.continuous.stronglyMeasurableAtFilter isOpen_Ioo x hx) (hf.continuousAt hx)).div_const _

lemma continuousOn_cumulative {f : ℝ → ℝ} {a b : ℝ} (hf : IntervalDensity f a b) (hab : a < b) :
    ContinuousOn (cumulative f a b) (Icc a b) := by
  have hc := intervalIntegral.continuousOn_primitive_interval' hf.integrable (a := a) left_mem_uIcc
  rw [uIcc_of_le hab.le] at hc
  exact hc.div_const _

lemma cumulative_strictMonoOn {f : ℝ → ℝ} {a b : ℝ} (hf : IntervalDensity f a b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) (hab : a < b) :
    StrictMonoOn (cumulative f a b) (Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b) (continuousOn_cumulative hf hab)
  intro x hx
  have hx' : x ∈ Ioo a b := by simpa only [interior_Icc] using hx
  rw [(cumulative_hasDerivAt hf hx').deriv]
  exact div_pos (hpos x hx') (integral_positive hf hpos hab)

@[simp] lemma cumulative_left (f : ℝ → ℝ) (a b : ℝ) : cumulative f a b a = 0 := by
  simp [cumulative]

lemma cumulative_right {f : ℝ → ℝ} {a b : ℝ} (hf : IntervalDensity f a b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) (hab : a < b) : cumulative f a b b = 1 := by
  simp only [cumulative, div_self (integral_positive hf hpos hab).ne']

lemma cumulative_surjOn {f : ℝ → ℝ} {a b : ℝ} (hf : IntervalDensity f a b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) (hab : a < b) :
    SurjOn (cumulative f a b) (Icc a b) (Icc 0 1) := by
  have h := (continuousOn_cumulative hf hab).surjOn_Icc
    (s:=Icc a b) (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le)
  simpa only [cumulative_left, cumulative_right hf hpos hab] using h

lemma quantile_mem {f : ℝ → ℝ} {a b p : ℝ} (hf : IntervalDensity f a b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) (hab : a < b) (hp : p ∈ Icc 0 1) :
    quantile f a b p ∈ Icc a b :=
  Function.invFunOn_mem (cumulative_surjOn hf hpos hab hp)

lemma cumulative_quantile {f : ℝ → ℝ} {a b p : ℝ} (hf : IntervalDensity f a b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) (hab : a < b) (hp : p ∈ Icc 0 1) :
    cumulative f a b (quantile f a b p) = p :=
  Function.invFunOn_eq (cumulative_surjOn hf hpos hab hp)

lemma quantile_cumulative {f : ℝ → ℝ} {a b x : ℝ} (hf : IntervalDensity f a b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) (hab : a < b) (hx : x ∈ Icc a b) :
    quantile f a b (cumulative f a b x) = x :=
  (cumulative_strictMonoOn hf hpos hab).injOn.leftInvOn_invFunOn hx

lemma quantile_left {f : ℝ → ℝ} {a b : ℝ} (hf : IntervalDensity f a b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) (hab : a < b) : quantile f a b 0 = a := by
  simpa only [cumulative_left] using
    quantile_cumulative hf hpos hab (left_mem_Icc.mpr hab.le)

lemma quantile_right {f : ℝ → ℝ} {a b : ℝ} (hf : IntervalDensity f a b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) (hab : a < b) : quantile f a b 1 = b := by
  simpa only [cumulative_right hf hpos hab] using
    quantile_cumulative hf hpos hab (right_mem_Icc.mpr hab.le)

lemma quantile_strictMonoOn {f : ℝ → ℝ} {a b : ℝ} (hf : IntervalDensity f a b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) (hab : a < b) :
    StrictMonoOn (quantile f a b) (Icc 0 1) := by
  intro p hp q hq hpq
  apply (cumulative_strictMonoOn hf hpos hab).lt_iff_lt
    (quantile_mem hf hpos hab hp) (quantile_mem hf hpos hab hq) |>.mp
  simpa only [cumulative_quantile hf hpos hab hp, cumulative_quantile hf hpos hab hq] using hpq

lemma quantile_mem_Ioo {f : ℝ → ℝ} {a b p : ℝ} (hf : IntervalDensity f a b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) (hab : a < b) (hp : p ∈ Ioo 0 1) :
    quantile f a b p ∈ Ioo a b := by
  have hm := quantile_strictMonoOn hf hpos hab
  constructor
  · simpa only [quantile_left hf hpos hab] using
      hm (show 0 ∈ Icc (0 : ℝ) 1 by norm_num) (Ioo_subset_Icc_self hp) hp.1
  · simpa only [quantile_right hf hpos hab] using
      hm (Ioo_subset_Icc_self hp) (show 1 ∈ Icc (0 : ℝ) 1 by norm_num) hp.2

lemma quantile_image_Ioo {f : ℝ → ℝ} {a b : ℝ} (hf : IntervalDensity f a b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) (hab : a < b) :
    quantile f a b '' Ioo 0 1 = Ioo a b := by
  apply Subset.antisymm
  · rintro x ⟨p,hp,rfl⟩
    exact quantile_mem_Ioo hf hpos hab hp
  · intro x hx
    refine ⟨cumulative f a b x, ?_, quantile_cumulative hf hpos hab (Ioo_subset_Icc_self hx)⟩
    have hm := cumulative_strictMonoOn hf hpos hab
    constructor
    · simpa only [cumulative_left] using hm (left_mem_Icc.mpr hab.le)
        (Ioo_subset_Icc_self hx) hx.1
    · simpa only [cumulative_right hf hpos hab] using hm (Ioo_subset_Icc_self hx)
        (right_mem_Icc.mpr hab.le) hx.2

lemma quantile_continuousAt {f : ℝ → ℝ} {a b p : ℝ} (hf : IntervalDensity f a b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) (hab : a < b) (hp : p ∈ Ioo 0 1) :
    ContinuousAt (quantile f a b) p := by
  apply ((quantile_strictMonoOn hf hpos hab).mono Ioo_subset_Icc_self).continuousAt_of_image_mem_nhds
    (isOpen_Ioo.mem_nhds hp)
  rw [quantile_image_Ioo hf hpos hab]
  exact isOpen_Ioo.mem_nhds (quantile_mem_Ioo hf hpos hab hp)

lemma quantile_hasDerivAt {f : ℝ → ℝ} {a b p : ℝ} (hf : IntervalDensity f a b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) (hab : a < b) (hp : p ∈ Ioo 0 1) :
    HasDerivAt (quantile f a b) ((∫ t in a..b, f t) / f (quantile f a b p)) p := by
  have hden : f (quantile f a b p) / (∫ t in a..b, f t) ≠ 0 :=
    (div_pos (hpos _ (quantile_mem_Ioo hf hpos hab hp)) (integral_positive hf hpos hab)).ne'
  have hh := (cumulative_hasDerivAt hf (quantile_mem_Ioo hf hpos hab hp)).of_local_left_inverse
    (quantile_continuousAt hf hpos hab hp) hden
    (by
      filter_upwards [isOpen_Ioo.mem_nhds hp] with q hq
      exact cumulative_quantile hf hpos hab (Ioo_subset_Icc_self hq))
  simpa only [inv_div] using hh

lemma cumulative_mem {f : ℝ → ℝ} {a b x : ℝ} (hf : IntervalDensity f a b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) (hab : a < b) (hx : x ∈ Icc a b) :
    cumulative f a b x ∈ Icc 0 1 := by
  have hm := (cumulative_strictMonoOn hf hpos hab).monotoneOn
  constructor
  · simpa only [cumulative_left] using hm (left_mem_Icc.mpr hab.le) hx hx.1
  · simpa only [cumulative_right hf hpos hab] using hm hx (right_mem_Icc.mpr hab.le) hx.2

lemma quantile_continuousOn {f : ℝ → ℝ} {a b : ℝ} (hf : IntervalDensity f a b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) (hab : a < b) :
    ContinuousOn (quantile f a b) (Icc 0 1) := by
  let e : Icc a b ≃ Icc (0 : ℝ) 1 := {
    toFun := fun x => ⟨cumulative f a b x, cumulative_mem hf hpos hab x.property⟩
    invFun := fun p => ⟨quantile f a b p, quantile_mem hf hpos hab p.property⟩
    left_inv := fun x => Subtype.ext (quantile_cumulative hf hpos hab x.property)
    right_inv := fun p => Subtype.ext (cumulative_quantile hf hpos hab p.property) }
  have he : Continuous e := by
    apply Continuous.subtype_mk
    exact (continuousOn_iff_continuous_domRestrict).mp (continuousOn_cumulative hf hab)
  have hi := he.continuous_symm_of_equiv_compact_to_t2
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_subtype_val.comp hi

end SliceTransport

end

end OAI
