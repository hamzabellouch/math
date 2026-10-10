import Mathlib
import OAI.Geometry.CubicTorus.Regularity.BVBlowupNormalMeasure

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

def intervalSmoothHat (b : ℝ → ℝ) (a c t : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..t-a, b u) - ∫ u in (0 : ℝ)..t-c, b u

lemma primitive_contDiff {b : ℝ → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ ∫ u in (0 : ℝ)..t, b u) := by
  have hd (t : ℝ) := intervalIntegral.integral_hasDerivAt_right
    (hb.continuous.intervalIntegrable 0 t) (hb.continuous.stronglyMeasurableAtFilter volume _)
    hb.continuous.continuousAt
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t ↦ (hd t).differentiableAt,?_⟩
  simpa only [funext (fun t ↦ (hd t).deriv)] using hb

lemma intervalSmoothHat_contDiff {b : ℝ → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (a c : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (intervalSmoothHat b a c) :=
  ((primitive_contDiff hb).comp (contDiff_id.sub contDiff_const)).sub
    ((primitive_contDiff hb).comp (contDiff_id.sub contDiff_const))

lemma intervalSmoothHat_hasDerivAt {b : ℝ → ℝ} (hb : Continuous b)
    (a c t : ℝ) : HasDerivAt (intervalSmoothHat b a c) (b (t-a)-b (t-c)) t := by
  have hd (x : ℝ) := intervalIntegral.integral_hasDerivAt_right
    (hb.intervalIntegrable 0 x) (hb.stronglyMeasurableAtFilter volume _) hb.continuousAt
  change HasDerivAt (fun x : ℝ ↦ (∫ u in (0 : ℝ)..x-a, b u) -
    ∫ u in (0 : ℝ)..x-c, b u) _ _
  simpa only [Function.comp_def,mul_one,id_eq,Pi.sub_def] using
    ((hd (t-a)).comp t ((hasDerivAt_id t).sub_const a)).sub
      ((hd (t-c)).comp t ((hasDerivAt_id t).sub_const c))

lemma intervalSmoothHat_eq_integral {b : ℝ → ℝ} (hb : Continuous b)
    (a c t : ℝ) : intervalSmoothHat b a c t = ∫ u in t-c..t-a, b u := by
  rw [intervalSmoothHat]
  have hh := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume) (hb.intervalIntegrable 0 (t-c)) (hb.intervalIntegrable (t-c) (t-a))
  linarith

lemma intervalSmoothHat_nonneg {b : ℝ → ℝ} (hb : Continuous b)
    (hb0 : ∀ t, 0 ≤ b t) {a c : ℝ} (hac : a ≤ c) (t : ℝ) :
    0 ≤ intervalSmoothHat b a c t := by
  rw [intervalSmoothHat_eq_integral hb]
  exact intervalIntegral.integral_nonneg (by linarith) (fun _ _ ↦ hb0 _)

lemma intervalSmoothHat_le_one {b : ℝ → ℝ} (hb : Continuous b)
    (hbi : Integrable b volume) (hb0 : ∀ t, 0 ≤ b t) (hb1 : ∫ t, b t = 1)
    {a c : ℝ} (hac : a ≤ c) (t : ℝ) : intervalSmoothHat b a c t ≤ 1 := by
  rw [intervalSmoothHat_eq_integral hb,intervalIntegral.integral_of_le (by linarith)]
  rw [← hb1]
  exact setIntegral_le_integral hbi (ae_of_all _ hb0)

lemma intervalSmoothHat_support {b : ℝ → ℝ} (hb : Continuous b)
    {r a c : ℝ} (hs : tsupport b ⊆ Icc (-r) r) (hac : a ≤ c) :
    tsupport (intervalSmoothHat b a c) ⊆ Icc (a-r) (c+r) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hh
  apply ht
  rw [intervalSmoothHat_eq_integral hb]
  apply intervalIntegral.integral_zero_ae
  apply ae_of_all
  intro u hu
  have htc : t-c ≤ t-a := by linarith
  rw [uIoc_of_le htc] at hu
  apply image_eq_zero_of_notMem_tsupport
  intro hub
  have hur := hs hub
  simp only [mem_Icc,not_and_or,not_le] at hh
  rcases hh with hl|hr
  · linarith [hu.2,hur.1]
  · linarith [hu.1,hur.2]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

def partitionSmoothTest (b : ℝ → ℝ) (u σ : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, σ i * intervalSmoothHat b (u i) (u (i+1)) t

lemma intervalSmoothHat_sum (b : ℝ → ℝ) (u : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    (∑ i ∈ Finset.range n, intervalSmoothHat b (u i) (u (i+1)) t) =
      intervalSmoothHat b (u 0) (u n) t := by
  induction n with
  | zero => simp [intervalSmoothHat]
  | succ n ih => rw [Finset.sum_range_succ,ih]; simp only [intervalSmoothHat]; ring

lemma partitionSmoothTest_contDiff {b : ℝ → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (u σ : ℕ → ℝ) (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (partitionSmoothTest b u σ n) := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul (intervalSmoothHat_contDiff hb _ _)

lemma partitionSmoothTest_deriv {b : ℝ → ℝ} (hb : Continuous b)
    (u σ : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    deriv (partitionSmoothTest b u σ n) t =
      ∑ i ∈ Finset.range n, σ i * (b (t-u i)-b (t-u (i+1))) := by
  have he : partitionSmoothTest b u σ n =
      ∑ i ∈ Finset.range n, (fun y ↦ σ i*intervalSmoothHat b (u i) (u (i+1)) y) := by
    ext y
    simp [partitionSmoothTest]
  rw [he]
  exact (HasDerivAt.sum (u := Finset.range n) (fun i _ ↦
    (intervalSmoothHat_hasDerivAt hb (u i) (u (i+1)) t).const_mul (σ i))).deriv

lemma partitionSmoothTest_bound {b : ℝ → ℝ} (hb : Continuous b)
    (hbi : Integrable b volume) (hb0 : ∀ t, 0 ≤ b t) (hb1 : ∫ t, b t = 1)
    {u σ : ℕ → ℝ} (hu : Monotone u) (hσ : ∀ i, |σ i| ≤ 1) (n : ℕ) (t : ℝ) :
    |partitionSmoothTest b u σ n t| ≤ 1 := by
  calc
    _ ≤ ∑ i ∈ Finset.range n, |σ i*intervalSmoothHat b (u i) (u (i+1)) t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, intervalSmoothHat b (u i) (u (i+1)) t := by
      apply Finset.sum_le_sum
      intro i _
      have hh := intervalSmoothHat_nonneg hb hb0 (hu (Nat.le_succ i)) t
      rw [abs_mul,abs_of_nonneg hh]
      exact mul_le_of_le_one_left hh (hσ i)
    _ = intervalSmoothHat b (u 0) (u n) t := intervalSmoothHat_sum _ _ _ _
    _ ≤ 1 := intervalSmoothHat_le_one hb hbi hb0 hb1 (hu (Nat.zero_le n)) t

lemma partitionSmoothTest_support {b : ℝ → ℝ} (hb : Continuous b)
    {r a c : ℝ} (hs : tsupport b ⊆ Icc (-r) r)
    {u σ : ℕ → ℝ} (hu : Monotone u) (hus : ∀ i, u i ∈ Icc a c) (n : ℕ) :
    tsupport (partitionSmoothTest b u σ n) ⊆ Icc (a-r) (c+r) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hh
  apply ht
  apply Finset.sum_eq_zero
  intro i _
  have hn : t ∉ tsupport (intervalSmoothHat b (u i) (u (i+1))) := by
    intro h
    have H := intervalSmoothHat_support hb hs (hu (Nat.le_succ i)) h
    exact hh ⟨by linarith [(hus i).1,H.1],by linarith [(hus (i+1)).2,H.2]⟩
  rw [image_eq_zero_of_notMem_tsupport hn,mul_zero]

lemma bounded_mul_shift_integrable {f b : ℝ → ℝ} (hf : Measurable f)
    (hf1 : ∀ t, |f t| ≤ 1) (hbi : Integrable b volume) (x : ℝ) :
    Integrable (fun t ↦ f t*b (t-x)) volume := by
  have hi : Integrable (fun t ↦ b (t-x)) volume := by
    simpa only [Function.comp_def,sub_eq_add_neg] using
      ((measurePreserving_add_right volume (-x)).integrable_comp hbi.aestronglyMeasurable).mpr hbi
  apply hi.norm.mono' (hf.aestronglyMeasurable.mul hi.aestronglyMeasurable)
  apply ae_of_all
  intro t
  change |f t*b (t-x)| ≤ |b (t-x)|
  rw [abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (hf1 t)

lemma partitionSmoothTest_flux {f b : ℝ → ℝ} (hf : Measurable f)
    (hf1 : ∀ t, |f t| ≤ 1) (hb : Continuous b) (hbi : Integrable b volume)
    (u σ : ℕ → ℝ) (n : ℕ) :
    (∫ t : ℝ, f t*deriv (partitionSmoothTest b u σ n) t) =
      ∑ i ∈ Finset.range n, σ i*((∫ t : ℝ, f t*b (t-u i))-
        ∫ t : ℝ, f t*b (t-u (i+1))) := by
  simp_rw [partitionSmoothTest_deriv hb,Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    simp_rw [show ∀ t : ℝ, f t*(σ i*(b (t-u i)-b (t-u (i+1)))) =
      σ i*(f t*b (t-u i)-f t*b (t-u (i+1))) by intro t; ring]
    rw [integral_const_mul,integral_sub (bounded_mul_shift_integrable hf hf1 hbi _)
      (bounded_mul_shift_integrable hf hf1 hbi _)]
  · intro i _
    convert ((bounded_mul_shift_integrable hf hf1 hbi (u i)).sub
      (bounded_mul_shift_integrable hf hf1 hbi (u (i+1)))).const_mul (σ i) using 1
    funext t
    simp only [Pi.sub_apply]
    ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma binary_tendsto_eventually_constant {α : Type*} {f : α → ℝ} {l : Filter α}
    {c : ℝ} (ht : Tendsto f l (𝓝 c)) (hb : ∀ᶠ x in l, f x=0 ∨ f x=1) :
    ∃ d : ℝ, (d=0 ∨ d=1) ∧ ∀ᶠ x in l, f x=d := by
  rcases Filter.eq_or_neBot l with hl|hl
  · exact ⟨0,Or.inl rfl,by simp [hl]⟩
  have hc : c ∈ ({0,1} : Set ℝ) := (Set.toFinite ({0,1} : Set ℝ)).isClosed.mem_of_tendsto ht
    (hb.mono (fun _ hx ↦ by simpa using hx))
  have he := ht.eventually (Metric.ball_mem_nhds c (by norm_num : (0 : ℝ)<1/2))
  refine ⟨c,by simpa using hc,?_⟩
  filter_upwards [he,hb] with x hx hxb
  have hh : |f x-c| < 1/2 := by simpa only [Metric.mem_ball,Real.dist_eq] using hx
  rcases (show c=0 ∨ c=1 by simpa using hc) with rfl|rfl <;>
    rcases hxb with he|he <;> simp_all <;> norm_num at *

lemma binary_bv_side_constants {f : ℝ → ℝ} {s : Set ℝ}
    (hf : BoundedVariationOn f s) (hb : ∀ x ∈ s, f x=0 ∨ f x=1) (x : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ a b : ℝ,
      (∀ y ∈ s, y ∈ Metric.ball x δ → y < x → f y=a) ∧
      (∀ y ∈ s, y ∈ Metric.ball x δ → x < y → f y=b) := by
  obtain ⟨a,ha⟩ := hf.exists_tendsto_left x
  obtain ⟨b,hb'⟩ := hf.exists_tendsto_right x
  obtain ⟨a',_,ha'⟩ := binary_tendsto_eventually_constant ha
    (Filter.Eventually.mono self_mem_nhdsWithin (fun y hy ↦ hb y hy.1))
  obtain ⟨b',_,hb''⟩ := binary_tendsto_eventually_constant hb'
    (Filter.Eventually.mono self_mem_nhdsWithin (fun y hy ↦ hb y hy.1))
  obtain ⟨δ,hδ,hleft⟩ := Metric.mem_nhdsWithin_iff.mp ha'
  obtain ⟨ε,hε,hright⟩ := Metric.mem_nhdsWithin_iff.mp hb''
  refine ⟨min δ ε,lt_min hδ hε,a',b',?_,?_⟩
  · exact fun y hy hyd hyx ↦ hleft ⟨(Metric.ball_subset_ball (min_le_left _ _)) hyd,hy,hyx⟩
  · exact fun y hy hyd hxy ↦ hright ⟨(Metric.ball_subset_ball (min_le_right _ _)) hyd,hy,hxy⟩

lemma binary_bv_punctured_continuity {f : ℝ → ℝ} {s : Set ℝ}
    (hf : BoundedVariationOn f s) (hb : ∀ x ∈ s, f x=0 ∨ f x=1) (x : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ s, y ∈ Metric.ball x δ → y ≠ x →
      ContinuousWithinAt f s y := by
  obtain ⟨δ,hδ,a,b,ha,hb'⟩ := binary_bv_side_constants hf hb x
  refine ⟨δ,hδ,?_⟩
  intro y hy hyb hyx
  rcases lt_or_gt_of_ne hyx with hlt|hgt
  · have he : ∀ᶠ z in 𝓝[s] y, f z=a := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds hyb),
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hlt)] with z hz hzb hzx
      exact ha z hz hzb hzx
    have ht : Tendsto f (𝓝[s] y) (𝓝 a) := tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he)
    simpa only [ContinuousWithinAt,ha y hy hyb hlt] using ht
  · have he : ∀ᶠ z in 𝓝[s] y, f z=b := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds hyb),
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hgt)] with z hz hzb hxz
      exact hb' z hz hzb hxz
    have ht : Tendsto f (𝓝[s] y) (𝓝 b) := tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he)
    simpa only [ContinuousWithinAt,hb' y hy hyb hgt] using ht

theorem binary_bv_finite_discontinuities {f : ℝ → ℝ} {s : Set ℝ}
    (hs : IsCompact s) (hf : BoundedVariationOn f s)
    (hb : ∀ x ∈ s, f x=0 ∨ f x=1) :
    {x ∈ s | ¬ ContinuousWithinAt f s x}.Finite := by
  by_contra hfin
  obtain ⟨x,_,hx⟩ := (show {x ∈ s | ¬ ContinuousWithinAt f s x}.Infinite from hfin).exists_accPt_of_subset_isCompact hs
    (show {x ∈ s | ¬ ContinuousWithinAt f s x} ⊆ s from fun _ hh ↦ hh.1)
  obtain ⟨δ,hδ,hd⟩ := binary_bv_punctured_continuity hf hb x
  obtain ⟨y,hy,hyx⟩ := accPt_iff_nhds.mp hx (Metric.ball x δ) (Metric.ball_mem_nhds x hδ)
  exact hy.2.2 (hd y hy.2.1 hy.1 hyx)

lemma eVariationOn_le_of_pointwise_tendsto {f : ℝ → ℝ} {g : ℕ → ℝ → ℝ}
    {s : Set ℝ} {K : ℝ≥0∞} (hg : ∀ i, eVariationOn (g i) s ≤ K)
    (ht : ∀ x ∈ s, Tendsto (fun i ↦ g i x) atTop (𝓝 (f x))) :
    eVariationOn f s ≤ K := by
  apply iSup_le
  rintro ⟨n,u,hu,hus⟩
  have hlim : Tendsto (fun j ↦ ∑ i ∈ Finset.range n,
      edist (g j (u (i+1))) (g j (u i))) atTop
      (𝓝 (∑ i ∈ Finset.range n, edist (f (u (i+1))) (f (u i)))) :=
    tendsto_finsetSum _ (fun i _ ↦ (ht _ (hus (i+1))).edist (ht _ (hus i)))
  exact le_of_tendsto hlim (Filter.Eventually.of_forall fun j ↦ (eVariationOn.sum_le hu hus).trans (hg j))

lemma locally_constant_not_mixed_closure {f : ℝ → ℝ} {s : Set ℝ}
    {y a ε : ℝ} (hε : 0 < ε)
    (hf : ∀ z ∈ s, z ∈ Metric.ball y ε → f z=a) :
    y ∉ closure {z ∈ s | f z=0} ∩ closure {z ∈ s | f z=1} := by
  rintro ⟨h0,h1⟩
  obtain ⟨z,hz,hz0⟩ := Metric.mem_closure_iff.mp h0 ε hε
  obtain ⟨w,hw,hw1⟩ := Metric.mem_closure_iff.mp h1 ε hε
  have ha0 := hf z hz.1 (by simpa only [Metric.mem_ball,dist_comm] using hz0)
  have ha1 := hf w hw.1 (by simpa only [Metric.mem_ball,dist_comm] using hw1)
  rw [hz.2] at ha0
  rw [hw.2] at ha1
  linarith

theorem binary_bv_finite_mixed_boundary {f : ℝ → ℝ} {s K : Set ℝ}
    (hf : BoundedVariationOn f s) (hb : ∀ x ∈ s, f x=0 ∨ f x=1)
    (hK : IsCompact K) :
    (K ∩ (closure {z ∈ s | f z=0} ∩ closure {z ∈ s | f z=1})).Finite := by
  let D : Set ℝ := closure {z ∈ s | f z=0} ∩ closure {z ∈ s | f z=1}
  have hlocal (x : ℝ) : ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ Metric.ball x δ, y ≠ x → y ∉ D := by
    obtain ⟨δ,hδ,a,b,ha,hb'⟩ := binary_bv_side_constants hf hb x
    refine ⟨δ,hδ,?_⟩
    intro y hy hyx
    rcases lt_or_gt_of_ne hyx with hlt|hgt
    · have hn : Metric.ball x δ ∩ Iio x ∈ 𝓝 y :=
        inter_mem (Metric.isOpen_ball.mem_nhds hy) (Iio_mem_nhds hlt)
      obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hn
      exact locally_constant_not_mixed_closure hε (fun z hz hze ↦
        ha z hz (hsub hze).1 (hsub hze).2)
    · have hn : Metric.ball x δ ∩ Ioi x ∈ 𝓝 y :=
        inter_mem (Metric.isOpen_ball.mem_nhds hy) (Ioi_mem_nhds hgt)
      obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hn
      exact locally_constant_not_mixed_closure hε (fun z hz hze ↦
        hb' z hz (hsub hze).1 (hsub hze).2)
  by_contra hfin
  obtain ⟨x,_,hx⟩ := (show (K ∩ D).Infinite from hfin).exists_accPt_of_subset_isCompact hK
    inter_subset_left
  obtain ⟨δ,hδ,hd⟩ := hlocal x
  obtain ⟨y,hy,hyx⟩ := accPt_iff_nhds.mp hx (Metric.ball x δ) (Metric.ball_mem_nhds x hδ)
  exact hd y hy.1 hyx hy.2.2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Convolution
namespace CubicTorus

theorem smoothed_variation_of_dual_bound {f b : ℝ → ℝ}
    (hf : Measurable f) (hf1 : ∀ t, |f t| ≤ 1)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbi : Integrable b volume)
    (hb0 : ∀ t, 0 ≤ b t) (hb1 : ∫ t, b t = 1)
    (hbs : tsupport b ⊆ Icc (-(1/8 : ℝ)) (1/8)) {L : ℝ}
    (hdual : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Ioo (-1 : ℝ) 1 → (∀ t, |ψ t| ≤ 1) →
      |∫ t : ℝ, f t*deriv ψ t| ≤ L) :
    eVariationOn (fun x : ℝ ↦ ∫ t : ℝ, f t*b (t-x)) (Icc (-(1/2 : ℝ)) (1/2)) ≤
      ENNReal.ofReal L := by
  let F : ℝ → ℝ := fun x ↦ ∫ t : ℝ, f t*b (t-x)
  apply iSup_le
  rintro ⟨n,u,hu,hus⟩
  let σ : ℕ → ℝ := fun i ↦ if 0 ≤ F (u i)-F (u (i+1)) then 1 else -1
  have hσ (i : ℕ) : |σ i| ≤ 1 := by dsimp [σ]; split_ifs <;> norm_num
  have he (i : ℕ) : σ i*(F (u i)-F (u (i+1))) = |F (u (i+1))-F (u i)| := by
    rw [abs_sub_comm]
    dsimp [σ]
    split_ifs with h
    · rw [one_mul,abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h)]; ring
  have hs : tsupport (partitionSmoothTest b u σ n) ⊆ Ioo (-1 : ℝ) 1 :=
    (partitionSmoothTest_support hb.continuous hbs hu hus n).trans
      (by intro t ht; constructor <;> linarith [ht.1,ht.2])
  have hh := hdual (partitionSmoothTest b u σ n) (partitionSmoothTest_contDiff hb u σ n)
    hs (partitionSmoothTest_bound hb.continuous hbi hb0 hb1 hu hσ n)
  rw [partitionSmoothTest_flux hf hf1 hb.continuous hbi] at hh
  change |∑ i ∈ Finset.range n, σ i*(F (u i)-F (u (i+1)))| ≤ L at hh
  simp_rw [he] at hh
  rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _))] at hh
  calc
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, |F (u (i+1))-F (u i)|) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ abs_nonneg _)]
      simp only [edist_dist,Real.dist_eq,F]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hh

def angularMollifier (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := 1/(16*((n : ℝ)+1))
  rOut := 2/(16*((n : ℝ)+1))
  rIn_pos := by positivity
  rIn_lt_rOut := by apply div_lt_div_of_pos_right (by norm_num); positivity

lemma angularMollifier_radius_tendsto :
    Tendsto (fun n ↦ (angularMollifier n).rOut) atTop (𝓝 0) := by
  have he (n : ℕ) : (angularMollifier n).rOut = (1/8 : ℝ)*(1/((n : ℝ)+1)) := by
    dsimp [angularMollifier]; field_simp; ring
  simp_rw [he]
  simpa only [mul_zero] using (tendsto_const_nhds (x := (1/8 : ℝ))).mul
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma angularMollifier_support (n : ℕ) :
    tsupport ((angularMollifier n).normed volume) ⊆ Icc (-(1/8 : ℝ)) (1/8) := by
  rw [(angularMollifier n).tsupport_normed_eq,Real.closedBall_eq_Icc]
  have hr : (angularMollifier n).rOut ≤ (1/8 : ℝ) := by
    change 2/(16*((n : ℝ)+1)) ≤ 1/8
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  intro t ht
  constructor <;> linarith [ht.1,ht.2]

lemma angular_smoothing_ae_tendsto {f : ℝ → ℝ} (hf : Measurable f)
    (hf1 : ∀ t, |f t| ≤ 1) :
    ∀ᵐ x : ℝ ∂volume, Tendsto
      (fun n ↦ ∫ t : ℝ, f t*(angularMollifier n).normed volume (t-x)) atTop (𝓝 (f x)) := by
  have hli : LocallyIntegrable f volume := by
    apply (continuous_const : Continuous (fun _ : ℝ ↦ (1 : ℝ))).locallyIntegrable.mono
      hf.aestronglyMeasurable
    exact ae_of_all _ (fun t ↦ by simpa only [Real.norm_eq_abs,abs_one] using hf1 t)
  have ht := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    angularMollifier_radius_tendsto (K := 2)
    (Eventually.of_forall fun n ↦ by dsimp [angularMollifier]; ring_nf; rfl) hli
  filter_upwards [ht] with x hx
  convert hx using 1
  funext n
  rw [convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply,smul_eq_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  change f t*(angularMollifier n).normed volume (t-x) =
      (angularMollifier n).normed volume (x-t)*f t
  rw [show x-t = -(t-x) by ring,(angularMollifier n).normed_neg]
  ring

theorem boundedVariationOn_good_set_of_dual_bound {f : ℝ → ℝ}
    (hf : Measurable f) (hf1 : ∀ t, |f t| ≤ 1) {L : ℝ}
    (hdual : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Ioo (-1 : ℝ) 1 → (∀ t, |ψ t| ≤ 1) →
      |∫ t : ℝ, f t*deriv ψ t| ≤ L) :
    ∃ s : Set ℝ, s ⊆ Icc (-(1/2 : ℝ)) (1/2) ∧
      (∀ᵐ x : ℝ ∂volume, x ∈ Icc (-(1/2 : ℝ)) (1/2) → x ∈ s) ∧
      BoundedVariationOn f s := by
  let s : Set ℝ := {x | x ∈ Icc (-(1/2 : ℝ)) (1/2) ∧ Tendsto
    (fun n ↦ ∫ t : ℝ, f t*(angularMollifier n).normed volume (t-x)) atTop (𝓝 (f x))}
  refine ⟨s,fun _ hx ↦ hx.1,(angular_smoothing_ae_tendsto hf hf1).mono (fun x hx hI ↦ ⟨hI,hx⟩),?_⟩
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  apply eVariationOn_le_of_pointwise_tendsto (K := ENNReal.ofReal L) _ (fun _ hx ↦ hx.2)
  intro n
  exact (eVariationOn.mono _ (show s ⊆ Icc (-(1/2 : ℝ)) (1/2) from fun _ hx ↦ hx.1)).trans
    (smoothed_variation_of_dual_bound hf hf1 (angularMollifier n).contDiff_normed
      (angularMollifier n).integrable_normed (angularMollifier n).nonneg_normed
      (angularMollifier n).integral_normed (angularMollifier_support n) hdual)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem totallyBounded_moving_blowupCharacteristic {ι : Type*} {E : Set Torus}
    (hE : MeasurableSet E) {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : ι → Cover) (r : ι → ℝ) (hr : ∀ i, 0 < r i) {R : ℝ} (hR : 0 < R)
    (hc : ∀ i, Metric.ball (c i) (r i*(R+1)) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1})
    {A : ℝ} (hA : 0 ≤ A)
    (harea : ∀ i, (spatialNormalMeasure μ : Measure Torus).real
      (Metric.ball (quotientMap (c i)) (r i*((R+1)+2))) ≤ A*(r i*((R+1)+2))^2) :
    TotallyBounded (range fun i ↦ boundedFunctionL1
      (volume.restrict (Metric.closedBall (0 : Cover) R)) (blowupCharacteristic E (c i) (r i))
      (measurable_blowupCharacteristic hE (c i) (r i)) (blowupCharacteristic_bound E (c i) (r i))) := by
  apply totallyBounded_local_translation (η := volume) (isCompact_closedBall _ _)
    (fun i ↦ blowupCharacteristic E (c i) (r i))
    (fun i ↦ measurable_blowupCharacteristic hE (c i) (r i))
    (fun i ↦ blowupCharacteristic_bound E (c i) (r i))
    (A := A*((R+1)+2)^2) (ε₀ := 1) (by positivity) (by norm_num)
  intro i y hy
  have htrans := blowupCharacteristic_translation_density hE hμ (c i) (hr i)
    (by linarith : 0 ≤ R+1) (hc i) hA (harea i) y hy
  apply le_trans _ htrans
  apply setIntegral_mono_set _ (ae_of_all _ fun _ ↦ abs_nonneg _)
    (ae_of_all _ fun _ hx ↦ Metric.closedBall_subset_ball (by linarith : R < R+1) hx)
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Cover) (R+1))) :=
    isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
  have hf := measurable_blowupCharacteristic hE (c i) (r i)
  have hbound := blowupCharacteristic_bound E (c i) (r i)
  apply Integrable.of_bound (μ := volume.restrict (Metric.ball (0 : Cover) (R+1)))
    (((hf.comp (measurable_id.sub_const y)).sub hf).abs.aestronglyMeasurable) 2
  apply ae_of_all
  intro x
  simp only [Real.norm_eq_abs,abs_abs,Function.comp_apply,id_eq,Pi.sub_apply]
  exact (abs_sub _ _).trans (by linarith [hbound (x-y),hbound x])

theorem isMinimizerAt_moving_blowup_limit {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (c : ℕ → Cover) {d : ℝ} (hd : 0 < d)
    (hc : ∀ i, Metric.ball (c i) d ⊆ {x | ∀ j, 0 < x j ∧ x j < 1})
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    {R : ℝ} (hR : 0 < R) :
    ∃ F : Set Cover, MeasurableSet F ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
        |blowupCharacteristic E (c (φ i)) (r (φ i)) x-F.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0) ∧
      ∀ᵐ x ∂volume.restrict (Metric.closedBall (0 : Cover) R),
        Tendsto (fun i ↦ blowupCharacteristic E (c (φ i)) (r (φ i)) x) atTop
          (𝓝 (F.indicator (fun _ ↦ (1 : ℝ)) x)) := by
  obtain ⟨S,A,hS,hA,harea⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  obtain ⟨μ,hμ⟩ := exists_normalMeasure hE hmin.1.2.ne
  have hsmall : 0 < min (d/(R+1)) (S/((R+1)+2)) := by positivity
  obtain ⟨k,hk⟩ := eventually_atTop.mp (hrlim.eventually (gt_mem_nhds hsmall))
  let cs : ℕ → Cover := fun i ↦ c (i+k)
  let s : ℕ → ℝ := fun i ↦ r (i+k)
  have hs (i) : 0 < s i := hr _
  have hsb (i) : s i < min (d/(R+1)) (S/((R+1)+2)) := hk _ (by omega)
  have hchart (i) : Metric.ball (cs i) (s i*(R+1)) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} := by
    apply (Metric.ball_subset_ball _).trans (hc (i+k))
    exact ((lt_div_iff₀ (by linarith : 0 < R+1)).mp
      ((hsb i).trans_le (min_le_left _ _))).le
  have hb (i) : (spatialNormalMeasure μ : Measure Torus).real
      (Metric.ball (quotientMap (cs i)) (s i*((R+1)+2))) ≤ A*(s i*((R+1)+2))^2 := by
    apply harea μ hμ _ _ (by have hh := hs i; positivity)
    exact ((lt_div_iff₀ (by linarith : 0 < (R+1)+2)).mp
      ((hsb i).trans_le (min_le_right _ _))).le
  have ht := totallyBounded_moving_blowupCharacteristic hE hμ cs s hs hR hchart hA.le hb
  obtain ⟨F,hF,φ,hφ,hconv,hae⟩ := exists_cover_indicator_limit
    (fun i ↦ blowupCharacteristic E (cs i) (s i))
    (fun i ↦ measurable_blowupCharacteristic hE (cs i) (s i))
    (fun i ↦ blowupCharacteristic_bound E (cs i) (s i))
    (fun i x ↦ characteristic_dichotomy E (quotientMap (cs i+s i • x))) ht
  refine ⟨F,hF,fun i ↦ φ i+k,fun i j hij ↦ Nat.add_lt_add_right (hφ hij) k,?_,hae⟩
  exact boundedFunctionL1_integral_tendsto
    (fun i ↦ blowupCharacteristic E (cs (φ i)) (s (φ i)))
    (fun i ↦ measurable_blowupCharacteristic hE (cs (φ i)) (s (φ i)))
    (fun i ↦ blowupCharacteristic_bound E (cs (φ i)) (s (φ i)))
    (measurable_const.indicator hF) (cover_indicator_bound F) hconv

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integral_closedBall_affine_scaling (f : Cover → ℝ) (a : Cover) {r : ℝ}
    (hr : 0 < r) (R : ℝ) :
    (∫ x in Metric.closedBall a (r*R), f x) =
      r^3 * ∫ y in Metric.closedBall (0 : Cover) R, f (a+r • y) := by
  have h := integral_cover_affine_scaling ((Metric.closedBall a (r*R)).indicator f) a hr
  rw [integral_indicator Metric.isClosed_closedBall.measurableSet] at h
  rw [h, ← integral_indicator Metric.isClosed_closedBall.measurableSet]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hm : r • x+a ∈ Metric.closedBall a (r*R) ↔ x ∈ Metric.closedBall (0 : Cover) R := by
    simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero,
      norm_smul, Real.norm_of_nonneg hr.le]
    exact mul_le_mul_iff_right₀ hr
  change (Metric.closedBall a (r*R)).indicator f (r • x+a) =
    (Metric.closedBall (0 : Cover) R).indicator (fun y ↦ f (a+r • y)) x
  by_cases hx : x ∈ Metric.closedBall (0 : Cover) R
  · rw [indicator_of_mem (hm.mpr hx),indicator_of_mem hx,add_comm]
  · rw [indicator_of_notMem ((not_congr hm).mpr hx),indicator_of_notMem hx]

lemma local_affine_integral_le {f : Cover → ℝ} {S R : ℝ} (p : Cover) {r : ℝ}
    (hr : 0 < r) (hi : IntegrableOn f (Metric.closedBall (0 : Cover) S))
    (hf : ∀ x, 0 ≤ f x)
    (hsub : Metric.closedBall p (r*R) ⊆ Metric.closedBall (0 : Cover) S) :
    (∫ x in Metric.closedBall (0 : Cover) R, f (p+r • x)) ≤
      r⁻¹^3*(∫ x in Metric.closedBall (0 : Cover) S, f x) := by
  have hs := setIntegral_mono_set hi (ae_of_all _ hf) (ae_of_all _ hsub)
  change (∫ x in Metric.closedBall p (r*R), f x) ≤
    ∫ x in Metric.closedBall (0 : Cover) S, f x at hs
  rw [integral_closedBall_affine_scaling f p hr R] at hs
  have hh := mul_le_mul_of_nonneg_left hs (pow_nonneg (inv_nonneg.mpr hr.le) 3)
  have he : r⁻¹^3*(r^3*(∫ x in Metric.closedBall (0 : Cover) R, f (p+r • x))) =
      ∫ x in Metric.closedBall (0 : Cover) R, f (p+r • x) := by field_simp
  rwa [he] at hh

lemma localL1_affine_tendsto {g : ℕ → Cover → ℝ} (hg : ∀ i, Measurable (g i))
    (hgb : ∀ i x, |g i x| ≤ 1) {f : Cover → ℝ} (hf : Measurable f)
    (hfb : ∀ x, |f x| ≤ 1) {S R : ℝ} {l : Filter ℕ}
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) S, |g i x-f x|) l (𝓝 0))
    (p : Cover) {r : ℝ} (hr : 0 < r)
    (hsub : Metric.closedBall p (r*R) ⊆ Metric.closedBall (0 : Cover) S) :
    Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
      |g i (p+r • x)-f (p+r • x)|) l (𝓝 0) := by
  apply squeeze_zero (fun _ ↦ integral_nonneg (fun _ ↦ abs_nonneg _))
    (fun i ↦ local_affine_integral_le p hr
      (((integrable_bounded_one (hg i) (hgb i)).sub (integrable_bounded_one hf hfb)).abs)
      (fun _ ↦ abs_nonneg _) hsub)
  simpa only [mul_zero,Pi.sub_apply] using hconv.const_mul (r⁻¹^3)

lemma blowupCharacteristic_affine (E : Set Torus) (c p x : Cover) (r s : ℝ) :
    blowupCharacteristic E c r (p+s • x) =
      blowupCharacteristic E (c+r • p) (r*s) x := by
  simp [blowupCharacteristic,smul_add,mul_smul,add_assoc]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

lemma finiteMeasure_real_closed_lower {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [HasOuterApproxClosed X] [OpensMeasurableSpace X]
    {l : Filter ℕ} [NeBot l] {μ : ℕ → FiniteMeasure X} {ν : FiniteMeasure X}
    (hlim : Tendsto μ l (𝓝 ν)) {s t : Set X} (ht : IsClosed t) (hst : s ⊆ t)
    {b : ℝ} (hb : Tendsto (fun i ↦ (μ i : Measure X).real s) l (𝓝 b)) :
    b ≤ (ν : Measure X).real t := by
  have hbpos : 0 ≤ b := ge_of_tendsto hb (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hb
  have heq (i) : ENNReal.ofReal ((μ i : Measure X).real s) = (μ i : Measure X) s :=
    ENNReal.ofReal_toReal (measure_ne_top _ _)
  change Tendsto (fun i ↦ ENNReal.ofReal ((μ i : Measure X).real s)) l (𝓝 (ENNReal.ofReal b)) at he
  simp_rw [heq] at he
  have hle : ENNReal.ofReal b ≤ (ν : Measure X) t := by
    rw [← he.limsup_eq]
    exact (limsup_le_limsup (Eventually.of_forall fun i ↦ measure_mono hst)).trans
      (FiniteMeasure.limsup_measure_closed_le_of_tendsto hlim ht)
  simpa only [ENNReal.toReal_ofReal hbpos,Measure.real] using ENNReal.toReal_mono (measure_ne_top _ _) hle

lemma finiteMeasure_real_open_upper {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [HasOuterApproxClosed X] [OpensMeasurableSpace X]
    {l : Filter ℕ} [NeBot l] {μ : ℕ → FiniteMeasure X} {ν : FiniteMeasure X}
    (hlim : Tendsto μ l (𝓝 ν)) {s : Set X} (hs : IsOpen s)
    {b : ℝ} (hb : Tendsto (fun i ↦ (μ i : Measure X).real s) l (𝓝 b)) :
    (ν : Measure X).real s ≤ b := by
  have hm : Tendsto (fun i ↦ (μ i : Measure X).real univ) l
      (𝓝 ((ν : Measure X).real univ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp (FiniteMeasure.continuous_mass.tendsto ν |>.comp hlim)
  have hh := finiteMeasure_real_closed_lower hlim hs.isClosed_compl (Subset.refl sᶜ)
    (show Tendsto (fun i ↦ (μ i : Measure X).real sᶜ) l
      (𝓝 ((ν : Measure X).real univ-b)) by
      simp_rw [measureReal_compl hs.measurableSet]
      exact hm.sub hb)
  rw [measureReal_compl hs.measurableSet] at hh
  linarith

lemma blowupNormalMeasure_ball (μ : FiniteMeasure NormalBundle) (c : Cover)
    {r ρ R : ℝ} (hr : 0 < r) (hρ : ρ ≤ R) :
    (blowupNormalMeasure μ c r R : Measure BlowupNormalBundle).real
      {z | z.1 ∈ Metric.ball (0 : Cover) ρ} = r⁻¹^2*cellBallMass μ c (r*ρ) := by
  have hm : MeasurableSet {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) ρ} :=
    Metric.isOpen_ball.measurableSet.preimage measurable_fst
  have he : blowupNormalMap c r ⁻¹' {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) ρ} ∩
      {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball c (r*R)} =
      {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball c (r*ρ)} := by
    ext z
    simp only [mem_inter_iff,mem_preimage,mem_ofPred_eq,blowupNormalMap_mem c hr ρ]
    exact ⟨And.left,fun hz ↦ ⟨hz,Metric.ball_subset_ball (mul_le_mul_of_nonneg_left hρ hr.le) hz⟩⟩
  unfold blowupNormalMeasure
  rw [FiniteMeasure.toMeasure_smul]
  change ((_ : Measure BlowupNormalBundle) _).toReal = _
  rw [Measure.smul_apply,ENNReal.smul_def,smul_eq_mul,ENNReal.toReal_mul,FiniteMeasure.toMeasure_map,
    Measure.map_apply (continuous_blowupNormalMap c r).measurable hm,
    FiniteMeasure.restrict_measure_eq,Measure.restrict_apply
      (hm.preimage (continuous_blowupNormalMap c r).measurable),he]
  simp only [ENNReal.coe_toReal,Real.coe_toNNReal _ (sq_nonneg _)]
  rfl

lemma blowupNormalMeasure_ball_tendsto {μ : FiniteMeasure NormalBundle}
    (c : Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    {l : Filter ℕ} (hrlim : Tendsto r l (𝓝 0)) {θ : ℝ}
    (hθ : Tendsto (fun t ↦ cellBallMass μ c t / t^2) (𝓝[>] 0) (𝓝 θ))
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    Tendsto (fun i ↦ (blowupNormalMeasure μ c (r i) R : Measure BlowupNormalBundle).real
      {z | z.1 ∈ Metric.ball (0 : Cover) ρ}) l (𝓝 (θ*ρ^2)) := by
  have ht : Tendsto (fun i ↦ r i*ρ) l (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using hrlim.mul_const ρ,
      Eventually.of_forall fun i ↦ mul_pos (hr i) hρ⟩
  have hh := (hθ.comp ht).mul_const (ρ^2)
  convert hh using 1
  funext i
  rw [blowupNormalMeasure_ball μ c (hr i) hρR]
  dsimp only [Function.comp_apply]
  field_simp [(hr i).ne',hρ.ne']

theorem blowup_limit_ball_mass {μ : FiniteMeasure NormalBundle}
    (c : Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    {l : Filter ℕ} [NeBot l] (hrlim : Tendsto r l (𝓝 0)) {θ : ℝ}
    (hθ : Tendsto (fun t ↦ cellBallMass μ c t / t^2) (𝓝[>] 0) (𝓝 θ))
    {R : ℝ} {ν : FiniteMeasure BlowupNormalBundle}
    (hν : Tendsto (fun i ↦ blowupNormalMeasure μ c (r i) R) l (𝓝 ν))
    {ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) :
    (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) ρ} = θ*ρ^2 := by
  apply le_antisymm
  · exact finiteMeasure_real_open_upper hν (Metric.isOpen_ball.preimage continuous_fst)
      (blowupNormalMeasure_ball_tendsto c r hr hrlim hθ hρ hρR.le)
  · have hlow (s : ℝ) (hs : s ∈ Ioo 0 ρ) : θ*s^2 ≤
        (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) ρ} := by
      apply (finiteMeasure_real_closed_lower hν
        (Metric.isClosed_closedBall.preimage continuous_fst)
        (show {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) s} ⊆
          {z | z.1 ∈ Metric.closedBall (0 : Cover) s} from fun _ hz ↦ Metric.ball_subset_closedBall hz)
        (blowupNormalMeasure_ball_tendsto c r hr hrlim hθ hs.1 (hs.2.trans hρR).le)).trans
      exact measureReal_mono (fun _ hz ↦ Metric.closedBall_subset_ball hs.2 hz)
    have hh : Tendsto (fun s : ℝ ↦ θ*s^2) (𝓝[<] ρ) (𝓝 (θ*ρ^2)) :=
      (continuous_const.mul (continuous_id.pow 2)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto hh
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hρ)] with s hs hs0
    exact hlow s ⟨hs0,hs⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

lemma normalBall_measure_of_real {ν : FiniteMeasure BlowupNormalBundle} {θ ρ : ℝ}
    (h : (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) ρ} = θ*ρ^2) :
    (ν : Measure BlowupNormalBundle) {z | z.1 ∈ Metric.ball (0 : Cover) ρ} = ENNReal.ofReal (θ*ρ^2) := by
  rw [← h,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma norm_sq_lt_iff {x : Cover} {t : ℝ} (ht : 0 < t) :
    ‖x‖^2 < t ↔ x ∈ Metric.ball (0 : Cover) (Real.sqrt t) := by
  rw [Metric.mem_ball,dist_zero_right]
  have hs := Real.sq_sqrt ht.le
  have hp := Real.sqrt_pos.mpr ht
  constructor <;> intro h <;> nlinarith [norm_nonneg x]

theorem squaredRadius_distribution {ν : FiniteMeasure BlowupNormalBundle} {θ : ℝ}
    (hθ : 0 ≤ θ)
    (hm : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) ρ} = θ*ρ^2) :
    Measure.map (fun z : BlowupNormalBundle ↦ ‖z.1‖^2)
      ((ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ Metric.ball (0 : Cover) 1}) =
      ENNReal.ofReal θ • volume.restrict (Ioo (0 : ℝ) 1) := by
  have hmap : Measurable (fun z : BlowupNormalBundle ↦ ‖z.1‖^2) := measurable_fst.norm.pow_const _
  have hb1 := normalBall_measure_of_real (hm 1 (by norm_num) le_rfl)
  simp only [one_pow,mul_one] at hb1
  apply ext_of_generate_finite (range (Iio : ℝ → Set ℝ))
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iio ℝ)) isPiSystem_Iio
  · rintro _ ⟨t,rfl⟩
    rw [Measure.map_apply hmap measurableSet_Iio,Measure.restrict_apply
      (measurableSet_Iio.preimage hmap),Measure.smul_apply,smul_eq_mul,
      Measure.restrict_apply measurableSet_Iio]
    by_cases ht : t ≤ 0
    · have he : (fun z : BlowupNormalBundle ↦ ‖z.1‖^2) ⁻¹' Iio t ∩
          {z | z.1 ∈ Metric.ball (0 : Cover) 1} = ∅ := by
        ext z
        simp only [mem_inter_iff,mem_preimage,mem_Iio,mem_empty_iff_false,iff_false,not_and]
        intro hz
        exact False.elim ((not_lt_of_ge (le_trans ht (sq_nonneg _))) hz)
      have hI : Iio t ∩ Ioo (0 : ℝ) 1 = ∅ := by
        ext x
        simp only [mem_inter_iff,mem_Iio,mem_Ioo,mem_empty_iff_false,iff_false,not_and]
        intro hx hx0 _
        linarith
      rw [he,hI,measure_empty,measure_empty,mul_zero]
    · have ht0 := lt_of_not_ge ht
      by_cases ht1 : 1 ≤ t
      · have he : (fun z : BlowupNormalBundle ↦ ‖z.1‖^2) ⁻¹' Iio t ∩
            {z | z.1 ∈ Metric.ball (0 : Cover) 1} = {z | z.1 ∈ Metric.ball (0 : Cover) 1} := by
          apply inter_eq_right.mpr
          intro z hz
          have hz' : ‖z.1‖ < 1 := by simpa only [mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hz
          change ‖z.1‖^2 < t
          nlinarith [norm_nonneg z.1]
        have hI : Iio t ∩ Ioo (0 : ℝ) 1 = Ioo 0 1 := inter_eq_right.mpr (fun _ hx ↦ hx.2.trans_le ht1)
        rw [he,hI,hb1,Real.volume_Ioo]
        norm_num
      · have htlt := lt_of_not_ge ht1
        have hs : Real.sqrt t ≤ 1 := by nlinarith [Real.sq_sqrt ht0.le,Real.sqrt_nonneg t]
        have he : (fun z : BlowupNormalBundle ↦ ‖z.1‖^2) ⁻¹' Iio t ∩
            {z | z.1 ∈ Metric.ball (0 : Cover) 1} =
            {z | z.1 ∈ Metric.ball (0 : Cover) (Real.sqrt t)} := by
          ext z
          change (‖z.1‖^2 < t ∧ z.1 ∈ Metric.ball (0 : Cover) 1) ↔ _
          rw [norm_sq_lt_iff ht0]
          exact ⟨And.left,fun hz ↦ ⟨hz,Metric.ball_subset_ball hs hz⟩⟩
        have hI : Iio t ∩ Ioo (0 : ℝ) 1 = Ioo 0 t := by ext x; simp only [mem_inter_iff,mem_Iio,mem_Ioo]; grind
        rw [he,hI,normalBall_measure_of_real (hm _ (Real.sqrt_pos.mpr ht0) hs),
          Real.sq_sqrt ht0.le,Real.volume_Ioo,sub_zero,ENNReal.ofReal_mul hθ]
  · rw [Measure.map_apply hmap MeasurableSet.univ,preimage_univ,Measure.restrict_apply MeasurableSet.univ,
      univ_inter,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply MeasurableSet.univ,univ_inter,hb1,
      Real.volume_Ioo]
    norm_num

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

lemma smoothTransition_deriv_pos {t : ℝ} (ht : t ∈ Ioo 0 1) :
    0 < deriv Real.smoothTransition t := by
  have he (x : ℝ) : HasDerivAt expNegInvGlue
      (x⁻¹^2*expNegInvGlue x) x := by
    simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) x
  have hd := (he t).div ((he t).add ((he (1-t)).comp t ((hasDerivAt_id t).const_sub 1)))
    (Real.smoothTransition.pos_denom t).ne'
  change HasDerivAt Real.smoothTransition _ t at hd
  rw [hd.deriv]
  have hu := expNegInvGlue.pos_of_pos ht.1
  have hv := expNegInvGlue.pos_of_pos (sub_pos.mpr ht.2)
  have hu' : 0 < t⁻¹^2*expNegInvGlue t := mul_pos (sq_pos_of_pos (inv_pos.mpr ht.1)) hu
  have hv' : 0 < (1-t)⁻¹^2*expNegInvGlue (1-t) :=
    mul_pos (sq_pos_of_pos (inv_pos.mpr (sub_pos.mpr ht.2))) hv
  apply div_pos _ (sq_pos_of_pos (Real.smoothTransition.pos_denom t))
  simp only [Pi.add_apply,Function.comp_apply] at *
  nlinarith [mul_pos hu' hv,mul_pos hu hv']

def radialBalance (t : ℝ) : ℝ :=
  Real.smoothTransition (1-t)-t*deriv Real.smoothTransition (1-t)

lemma continuous_radialBalance : Continuous radialBalance :=
  (Real.smoothTransition.continuous.comp (continuous_const.sub continuous_id)).sub
    (continuous_id.mul (((Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num)).comp
      (continuous_const.sub continuous_id)))

lemma integral_radialBalance : (∫ t : ℝ in Ioo 0 1, radialBalance t) = 0 := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ ↦ s*Real.smoothTransition (1-s)) (radialBalance t) t := by
    have hh := (hasDerivAt_id t).mul
      (((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) (1-t)).hasDerivAt.comp t
        ((hasDerivAt_id t).const_sub 1))
    exact hh.congr_deriv (by dsimp [radialBalance]; ring)
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
      (continuous_radialBalance.intervalIntegrable 0 1)]
  simp

lemma radialBalance_zero {t : ℝ} (ht : 1 ≤ t) : radialBalance t = 0 := by
  rw [radialBalance,Real.smoothTransition.zero_of_nonpos (by linarith),
    smoothTransition_deriv_zero_of_nonpos (by linarith),mul_zero,sub_zero]

lemma quadraticMass_radialBalance {ν : FiniteMeasure BlowupNormalBundle} {θ : ℝ}
    (hθ : 0 ≤ θ)
    (hm : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) ρ} = θ*ρ^2) :
    (∫ z : BlowupNormalBundle, radialBalance (‖z.1‖^2) ∂(ν : Measure BlowupNormalBundle)) = 0 := by
  have hmap : Measurable (fun z : BlowupNormalBundle ↦ ‖z.1‖^2) := measurable_fst.norm.pow_const _
  have he := integral_map (μ := (ν : Measure BlowupNormalBundle).restrict
    {z | z.1 ∈ Metric.ball (0 : Cover) 1}) hmap.aemeasurable
      continuous_radialBalance.measurable.aestronglyMeasurable
  rw [squaredRadius_distribution hθ hm,integral_smul_measure,integral_radialBalance,smul_zero] at he
  have hz : ∀ z : BlowupNormalBundle, z ∉ {z | z.1 ∈ Metric.ball (0 : Cover) 1} →
      radialBalance (‖z.1‖^2) = 0 := by
    intro z hz
    apply radialBalance_zero
    have hh : 1 ≤ ‖z.1‖ := by simpa only [mem_ofPred_eq,Metric.mem_ball,dist_zero_right,not_lt] using hz
    nlinarith
  have hg := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := (ν : Measure BlowupNormalBundle)) hz
  exact hg.symm.trans he.symm

lemma integrable_radialTangency (ν : FiniteMeasure BlowupNormalBundle) :
    Integrable (fun z : BlowupNormalBundle ↦ radialDensitySlope 0 1 1 z.1*⟪(z.2 : Cover),z.1⟫^2)
      (ν : Measure BlowupNormalBundle) := by
  let g : BlowupNormalBundle → ℝ := fun z ↦ radialDensitySlope 0 1 1 z.1*⟪(z.2 : Cover),z.1⟫^2
  have hgcont : Continuous g := by
    apply ((continuous_radialDensitySlope 0 1 1).comp continuous_fst).mul
    exact ((continuous_subtype_val.comp continuous_snd).inner continuous_fst).pow 2
  have hgs : HasCompactSupport g := by
    apply (isCompact_closedBall (0 : Cover) 1 |>.prod (isCompact_univ : IsCompact (univ : Set NormalSphere))).of_isClosed_subset
      isClosed_closure
    apply closure_minimal _ (Metric.isClosed_closedBall.prod isClosed_univ)
    intro z hz
    refine ⟨?_,mem_univ _⟩
    by_contra hh
    apply hz
    have hb' : 1 < ‖z.1‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hh
    have hb : 1 ≤ ‖z.1-(0 : Cover)‖ := by simpa only [sub_zero] using hb'.le
    simp [g,radialDensitySlope_zero (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 1) hb]
  exact hgcont.integrable_of_hasCompactSupport (μ := (ν : Measure BlowupNormalBundle)) hgs

lemma integrable_radialBalanceNorm (ν : FiniteMeasure BlowupNormalBundle) :
    Integrable (fun z : BlowupNormalBundle ↦ radialBalance (‖z.1‖^2))
      (ν : Measure BlowupNormalBundle) := by
  have hbcont : Continuous (fun z : BlowupNormalBundle ↦ radialBalance (‖z.1‖^2)) :=
    continuous_radialBalance.comp (continuous_fst.norm.pow 2)
  have hbs : HasCompactSupport (fun z : BlowupNormalBundle ↦ radialBalance (‖z.1‖^2)) := by
    apply (isCompact_closedBall (0 : Cover) 1 |>.prod (isCompact_univ : IsCompact (univ : Set NormalSphere))).of_isClosed_subset
      isClosed_closure
    apply closure_minimal _ (Metric.isClosed_closedBall.prod isClosed_univ)
    intro z hz
    refine ⟨?_,mem_univ _⟩
    by_contra hh
    apply hz
    apply radialBalance_zero
    have hb : 1 < ‖z.1‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hh
    nlinarith
  exact hbcont.integrable_of_hasCompactSupport (μ := (ν : Measure BlowupNormalBundle)) hbs

lemma tangentialDivergence_radialBalance (z : BlowupNormalBundle) :
    tangentialDivergence (radialDensityField 0 1 1) z.1 z.2 =
      2*radialBalance (‖z.1‖^2)+2*(radialDensitySlope 0 1 1 z.1*⟪(z.2 : Cover),z.1⟫^2) := by
  rw [tangentialDivergence_radialDensityField z.2.property]
  simp only [radialBalance,radialDensityWeight,radialDensitySlope,sublevelCutoff,one_pow,sub_zero,div_one]
  ring

theorem stationary_quadraticMass_radial_tangent {ν : FiniteMeasure BlowupNormalBundle}
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hm : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) ρ} = θ*ρ^2)
    (hstat : ∀ (F : Cover → Cover), ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0) :
    ∀ᵐ z ∂(ν : Measure BlowupNormalBundle), z.1 ∈ Metric.ball (0 : Cover) 1 →
      ⟪(z.2 : Cover),z.1⟫ = 0 := by
  have hs := hstat (radialDensityField 0 1 1) (radialDensityField_contDiff 0 1 1)
    (radialDensityField_tsupport (by norm_num) (by norm_num))
  let g : BlowupNormalBundle → ℝ := fun z ↦ radialDensitySlope 0 1 1 z.1*⟪(z.2 : Cover),z.1⟫^2
  have hgi : Integrable g (ν : Measure BlowupNormalBundle) := integrable_radialTangency ν
  have hbi := integrable_radialBalanceNorm ν
  have he (z : BlowupNormalBundle) : tangentialDivergence (radialDensityField 0 1 1) z.1 z.2 =
      2*radialBalance (‖z.1‖^2)+2*g z := tangentialDivergence_radialBalance z
  simp_rw [he] at hs
  rw [integral_add (hbi.const_mul 2) (hgi.const_mul 2),integral_const_mul,integral_const_mul,
    quadraticMass_radialBalance hθ hm] at hs
  have hzero : (∫ z, g z ∂(ν : Measure BlowupNormalBundle)) = 0 := by linarith
  have hgn : ∀ z, 0 ≤ g z := fun z ↦
    mul_nonneg (radialDensitySlope_nonneg (0 : Cover) 1 (by norm_num : (0 : ℝ) < 1) z.1) (sq_nonneg _)
  have hae : ∀ᵐ z ∂(ν : Measure BlowupNormalBundle), g z = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (ae_of_all (ν : Measure BlowupNormalBundle) hgn) hgi).mp hzero
  filter_upwards [hae] with z hz hzball
  by_cases hx : z.1 = 0
  · simp [hx]
  · have hn : 0 < ‖z.1‖ := norm_pos_iff.mpr hx
    have hb : ‖z.1‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hzball
    have hp : 0 < radialDensitySlope 0 1 1 z.1 := by
      simp only [radialDensitySlope,one_pow,sub_zero,div_one]
      exact smoothTransition_deriv_pos ⟨by nlinarith,by nlinarith⟩
    have hsq : ⟪(z.2 : Cover),z.1⟫^2 = 0 := (mul_eq_zero.mp hz).resolve_left hp.ne'
    exact sq_eq_zero_iff.mp hsq

end CubicTorus

end
end

end

end OAI
