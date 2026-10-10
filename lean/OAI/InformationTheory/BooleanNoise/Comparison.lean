import OAI.InformationTheory.BooleanNoise.Basic
import OAI.InformationTheory.BooleanNoise.EntropyScalars
import OAI.InformationTheory.BooleanNoise.CurvatureCertificates
import OAI.InformationTheory.BooleanNoise.ComparisonEstimates
import OAI.InformationTheory.BooleanNoise.InverseRegularity
import OAI.InformationTheory.BooleanNoise.LShape
import OAI.InformationTheory.BooleanNoise.EntropyBounds
import OAI.InformationTheory.BooleanNoise.SemigroupFlow
import OAI.InformationTheory.BooleanNoise.CubeVariance
import OAI.InformationTheory.BooleanNoise.MonotoneDissipation
import OAI.InformationTheory.BooleanNoise.GeneralDissipation
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

namespace OAI

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace LeanBlast.CourtadeKumar

theorem le_add_initial_gap_of_deriv_le_on_above
    {f g f' g' : ℝ → ℝ} {a b δ : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t)
    (hderiv : ∀ t ∈ Ico a b, g t ≤ f t → f' t ≤ g' t)
    (hδ : 0 ≤ δ) (ha : f a ≤ g a + δ) :
    ∀ t ∈ Icc a b, f t ≤ g t + δ := by
  have hfcont : ContinuousOn f (Icc a b) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hgcont : ContinuousOn g (Icc a b) :=
    fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hpert : ∀ t ∈ Icc a b, ∀ ε > 0,
      f t ≤ g t + δ + ε * (t - a) := by
    intro t ht ε hε
    apply image_le_of_deriv_right_lt_deriv_boundary' hfcont
      (fun x hx => (hf x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt)
      (B := fun x => g x + δ + ε * (x - a))
      (B' := fun x => g' x + ε)
    · simpa using ha
    · exact (hgcont.add continuousOn_const).add
        (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
    · intro x hx
      convert! (((hg x ⟨hx.1, hx.2.le⟩).add_const δ).add
        (((hasDerivAt_id x).sub_const a).const_mul ε)).hasDerivWithinAt using 1
      simp
    · intro x hx heq
      have hnonneg : 0 ≤ ε * (x - a) := mul_nonneg hε.le (sub_nonneg.mpr hx.1)
      have hgf : g x ≤ f x := by rw [heq]; linarith
      have hd := hderiv x hx hgf
      linarith
    · exact ht
  intro t ht
  have hc : ContinuousWithinAt (fun ε : ℝ => g t + δ + ε * (t - a)) (Ioi 0) 0 := by
    fun_prop
  convert continuousWithinAt_const.closure_le _ hc (hpert t ht) using 1 <;> simp

theorem le_of_deriv_le_on_above
    {f g f' g' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t)
    (hderiv : ∀ t ∈ Ico a b, g t ≤ f t → f' t ≤ g' t)
    (ha : f a ≤ g a) : ∀ t ∈ Icc a b, f t ≤ g t := by
  simpa only [add_zero] using
    le_add_initial_gap_of_deriv_le_on_above hf hg hderiv (δ := 0) le_rfl (by simpa using ha)

theorem le_of_deriv_le_on_above_of_tendsto
    {f g f' g' : ℝ → ℝ} {l : ℝ}
    (hf : ∀ t, 0 < t → HasDerivAt f (f' t) t)
    (hg : ∀ t, 0 < t → HasDerivAt g (g' t) t)
    (hderiv : ∀ t, 0 < t → g t ≤ f t → f' t ≤ g' t)
    (hf0 : Tendsto f (𝓝[>] 0) (𝓝 l))
    (hg0 : Tendsto g (𝓝[>] 0) (𝓝 l)) :
    ∀ t, 0 < t → f t ≤ g t := by
  intro t ht
  have hlim : Tendsto (fun a => g t + max (f a - g a) 0) (𝓝[>] 0) (𝓝 (g t)) := by
    convert tendsto_const_nhds.add ((hf0.sub hg0).max tendsto_const_nhds) using 1
    simp
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [Ioo_mem_nhdsGT ht] with a ha
  apply le_add_initial_gap_of_deriv_le_on_above
    (fun x hx => hf x (ha.1.trans_le hx.1))
    (fun x hx => hg x (ha.1.trans_le hx.1))
    (fun x hx => hderiv x (ha.1.trans_le hx.1))
    (le_max_right (f a - g a) 0)
  · have hgmax := le_max_left (f a - g a) 0
    linarith
  · exact ⟨ha.2.le, le_rfl⟩

def comparisonKernel (s : ℝ) : ℝ := 1 / (s ^ 2 * Real.artanh s)

def comparisonV (u : ℝ) : ℝ :=
  2 * u * Real.artanh u * ∫ s in u..1, comparisonKernel s

def comparisonVTime (t : ℝ) : ℝ := comparisonV (Real.exp (-t))

theorem measurable_comparisonKernel : Measurable comparisonKernel := by
  unfold comparisonKernel Real.artanh
  fun_prop

theorem comparisonKernel_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ comparisonKernel s := by
  exact one_div_nonneg.mpr (mul_nonneg (sq_nonneg s) (Real.artanh_nonneg hs))

@[simp] theorem comparisonKernel_one : comparisonKernel 1 = 0 := by
  norm_num [comparisonKernel, Real.artanh]

theorem comparisonKernel_le {u s : ℝ} (hu : 0 < u) (hu1 : u < 1)
    (hus : u ≤ s) (hs1 : s ≤ 1) : comparisonKernel s ≤ comparisonKernel u := by
  by_cases hs : s = 1
  · subst s
    simpa using comparisonKernel_nonneg hu.le
  · have hslt : s < 1 := lt_of_le_of_ne hs1 hs
    apply one_div_le_one_div_of_le
      (mul_pos (sq_pos_of_pos hu) (Real.artanh_pos ⟨hu, hu1⟩))
    exact mul_le_mul (sq_le_sq₀ hu.le (hu.le.trans hus) |>.mpr hus)
      (Real.artanh_le_artanh (by linarith) hslt hus)
      (Real.artanh_nonneg hu.le) (sq_nonneg s)

theorem intervalIntegrable_comparisonKernel {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    IntervalIntegrable comparisonKernel volume u 1 := by
  apply (intervalIntegrable_const (c := comparisonKernel u)).mono_fun'
    measurable_comparisonKernel.aestronglyMeasurable
  rw [uIoc_of_le hu1.le]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (comparisonKernel_nonneg (hu.le.trans hs.1.le))]
  exact comparisonKernel_le hu hu1 hs.1.le hs.2

theorem continuousAt_comparisonKernel {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ContinuousAt comparisonKernel u := by
  exact continuousAt_const.div
    ((continuousAt_id.pow 2).mul (hasDerivAt_artanh ⟨by linarith, hu1⟩).continuousAt)
    (mul_ne_zero (pow_ne_zero 2 hu.ne') (ne_of_gt (Real.artanh_pos ⟨hu, hu1⟩)))

theorem comparisonV_nonneg {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ comparisonV u := by
  apply mul_nonneg
  · exact mul_nonneg (mul_nonneg (by norm_num) hu) (Real.artanh_nonneg hu)
  · exact intervalIntegral.integral_nonneg hu1 fun s hs =>
      comparisonKernel_nonneg (hu.trans hs.1)

theorem comparisonV_le_endpoint_bound {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    comparisonV u ≤ 2 * (1 - u) / u := by
  have hI : (∫ s in u..1, comparisonKernel s) ≤ (1 - u) * comparisonKernel u := by
    calc
      _ ≤ ∫ _s in u..1, comparisonKernel u :=
        intervalIntegral.integral_mono_on hu1.le (intervalIntegrable_comparisonKernel hu hu1)
          intervalIntegrable_const (fun s hs => comparisonKernel_le hu hu1 hs.1 hs.2)
      _ = _ := by simp
  unfold comparisonV
  calc
    _ ≤ 2 * u * Real.artanh u * ((1 - u) * comparisonKernel u) :=
      mul_le_mul_of_nonneg_left hI
        (mul_nonneg (mul_nonneg (by norm_num) hu.le) (Real.artanh_nonneg hu.le))
    _ = 2 * (1 - u) / u := by
      unfold comparisonKernel
      field_simp [hu.ne', (Real.artanh_pos ⟨hu, hu1⟩).ne']

theorem tendsto_comparisonVTime_zero :
    Tendsto comparisonVTime (𝓝[>] 0) (𝓝 0) := by
  have hu : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[>] 0) (𝓝 1) := by
    have h : Continuous (fun t : ℝ => Real.exp (-t)) := by fun_prop
    simpa using (h.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hbound : Tendsto (fun t : ℝ => 2 * (1 - Real.exp (-t)) / Real.exp (-t))
      (𝓝[>] 0) (𝓝 0) := by
    convert (tendsto_const_nhds.mul (tendsto_const_nhds.sub hu)).div hu (by norm_num) using 1
    norm_num
  apply squeeze_zero' _ _ hbound
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    exact comparisonV_nonneg (Real.exp_pos _).le (le_of_lt (Real.exp_lt_one_iff.mpr (by linarith)))
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    exact comparisonV_le_endpoint_bound (Real.exp_pos _) (Real.exp_lt_one_iff.mpr (by linarith))

theorem hasDerivAt_comparisonV {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    HasDerivAt comparisonV
      (2 * (Real.artanh u + u / (1 - u ^ 2)) *
        (∫ s in u..1, comparisonKernel s) - 2 / u) u := by
  have hI := intervalIntegral.integral_hasDerivAt_left
    (intervalIntegrable_comparisonKernel hu hu1)
    measurable_comparisonKernel.stronglyMeasurable.stronglyMeasurableAtFilter
    (continuousAt_comparisonKernel hu hu1)
  have hprod := (((hasDerivAt_id u).const_mul 2).mul
    (hasDerivAt_artanh ⟨by linarith, hu1⟩)).mul hI
  convert! hprod using 1
  simp only [id_eq, Pi.mul_apply]
  unfold comparisonKernel
  field_simp [hu.ne', (Real.artanh_pos ⟨hu, hu1⟩).ne']
  ring

theorem hasDerivAt_comparisonVTime {t : ℝ} (ht : 0 < t) :
    let u := Real.exp (-t)
    HasDerivAt comparisonVTime
      (2 - (1 + u / ((1 - u ^ 2) * Real.artanh u)) * comparisonVTime t) t := by
  dsimp only
  have hu := Real.exp_pos (-t)
  have hu1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hderiv := (hasDerivAt_comparisonV hu hu1).comp t (hasDerivAt_id t).neg.exp
  convert! hderiv using 1
  simp only [id_eq, Pi.neg_apply]
  unfold comparisonVTime comparisonV
  have hden : 1 - Real.exp (-t) ^ 2 ≠ 0 := by nlinarith
  field_simp [hu.ne', (Real.artanh_pos ⟨hu, hu1⟩).ne', hden]
  ring

private theorem sq_lt_one_of_mem {u : ℝ} (hu : u ∈ Ioo (-1) 1) : u ^ 2 < 1 := by
  have hp : 0 < (1 - u) * (u + 1) := mul_pos (by linarith [hu.2]) (by linarith [hu.1])
  nlinarith

private theorem hasDerivAt_artanh_cubic_gap {u : ℝ} (hu : u ∈ Ioo (-1) 1) :
    HasDerivAt (fun x : ℝ => Real.artanh x - x - x ^ 3 / 3)
      (u ^ 4 / (1 - u ^ 2)) u := by
  have hden : 1 - u ^ 2 ≠ 0 := ne_of_gt (sub_pos.mpr (sq_lt_one_of_mem hu))
  convert! ((hasDerivAt_artanh hu).sub (hasDerivAt_id u)).sub
    (((hasDerivAt_id u).pow 3).div_const 3) using 1
  simp only [id_eq]
  field_simp [hden]
  ring

theorem artanh_cubic_lower {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) :
    u + u ^ 3 / 3 ≤ Real.artanh u := by
  have hm : MonotoneOn (fun x : ℝ => Real.artanh x - x - x ^ 3 / 3) (Ico 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
    · intro x hx
      exact (hasDerivAt_artanh_cubic_gap ⟨by linarith [hx.1], hx.2⟩).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : x ∈ Ico (0 : ℝ) 1 := interior_subset hx
      exact (hasDerivAt_artanh_cubic_gap ⟨by linarith [hx'.1], hx'.2⟩).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Ico (0 : ℝ) 1 := interior_subset hx
      exact div_nonneg (by positivity)
        (sub_nonneg.mpr (le_of_lt (sq_lt_one_of_mem ⟨by linarith [hx'.1], hx'.2⟩)))
  have h := hm (show (0 : ℝ) ∈ Ico 0 1 by norm_num) ⟨hu, hu1⟩ hu
  simp only [Real.artanh_zero, sub_zero] at h
  linarith

def rationalArtanhGap (u : ℝ) : ℝ := u / (1 - u ^ 2 / 2) - Real.artanh u

theorem hasDerivAt_rationalArtanhGap {u : ℝ} (hu : u ∈ Ioo (-1) 1) :
    HasDerivAt rationalArtanhGap
      (u ^ 2 * (2 - 3 * u ^ 2) / ((2 - u ^ 2) ^ 2 * (1 - u ^ 2))) u := by
  have hsq := sq_lt_one_of_mem hu
  have hden : 1 - u ^ 2 / 2 ≠ 0 := by nlinarith
  have hden' : 1 - u ^ 2 ≠ 0 := by nlinarith
  have hden'' : 2 - u ^ 2 ≠ 0 := by nlinarith
  have hd := ((hasDerivAt_id u).div
    ((hasDerivAt_const u 1).sub (((hasDerivAt_id u).pow 2).div_const 2)) hden).sub
      (hasDerivAt_artanh hu)
  convert! hd using 1
  simp only [id_eq, Pi.sub_apply, Pi.pow_apply]
  field_simp [hden, hden', hden'']
  ring

theorem artanh_le_rational {u : ℝ} (hu : 0 ≤ u) (hu9 : u ≤ 9 / 10) :
    Real.artanh u ≤ u / (1 - u ^ 2 / 2) := by
  let c : ℝ := Real.sqrt (2 / 3)
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hcsq : c ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  have hc9 : c < 9 / 10 := by nlinarith
  have hdenpos : ∀ x ∈ Icc (0 : ℝ) (9 / 10),
      0 < (2 - x ^ 2) ^ 2 * (1 - x ^ 2) := by
    intro x hx
    have hsq : x ^ 2 < 1 := sq_lt_one_of_mem ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact mul_pos (sq_pos_of_pos (by linarith)) (by linarith)
  have hleft : MonotoneOn rationalArtanhGap (Icc 0 c) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 c)
    · intro x hx
      exact (hasDerivAt_rationalArtanhGap ⟨by linarith [hx.1], by linarith [hx.2]⟩).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : x ∈ Icc (0 : ℝ) c := interior_subset hx
      exact (hasDerivAt_rationalArtanhGap ⟨by linarith [hx'.1], by linarith [hx'.2]⟩).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Icc (0 : ℝ) c := interior_subset hx
      have hsq : x ^ 2 ≤ c ^ 2 := (sq_le_sq₀ hx'.1 hc0).mpr hx'.2
      exact div_nonneg (mul_nonneg (sq_nonneg _) (by nlinarith))
        (hdenpos x ⟨hx'.1, hx'.2.trans hc9.le⟩).le
  have hright : AntitoneOn rationalArtanhGap (Icc c (9 / 10)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc c (9 / 10))
    · intro x hx
      exact (hasDerivAt_rationalArtanhGap ⟨by linarith [hx.1], by linarith [hx.2]⟩).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : x ∈ Icc c (9 / 10 : ℝ) := interior_subset hx
      exact (hasDerivAt_rationalArtanhGap ⟨by linarith [hx'.1], by linarith [hx'.2]⟩).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Icc c (9 / 10 : ℝ) := interior_subset hx
      have hx0 : 0 ≤ x := hc0.trans hx'.1
      have hsq : c ^ 2 ≤ x ^ 2 := (sq_le_sq₀ hc0 hx0).mpr hx'.1
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by nlinarith))
        (hdenpos x ⟨hx0, hx'.2⟩).le
  have hend : 0 ≤ rationalArtanhGap (9 / 10) := by
    have ha : Real.artanh (9 / 10) = Real.log 19 / 2 := by
      rw [Real.artanh_eq_half_log (by norm_num)]
      norm_num
      ring
    unfold rationalArtanhGap
    rw [ha]
    norm_num
    linarith [log_nineteen_lt_three]
  have hgap : 0 ≤ rationalArtanhGap u := by
    by_cases huc : u ≤ c
    · have h := hleft ⟨le_rfl, hc0⟩ ⟨hu, huc⟩ hu
      simpa [rationalArtanhGap] using h
    · exact hend.trans (hright ⟨le_of_not_ge huc, hu9⟩ ⟨hc9.le, le_rfl⟩ hu9)
  exact sub_nonneg.mp hgap

def comparisonModelKernel (s : ℝ) : ℝ := (1 - s ^ 2 / 2) / s ^ 3

def comparisonPrimitive (s : ℝ) : ℝ := -(1 / (2 * s ^ 2)) - Real.log s / 2

theorem comparisonModelKernel_le {s : ℝ} (hs : 0 < s) (hs9 : s ≤ 9 / 10) :
    comparisonModelKernel s ≤ comparisonKernel s := by
  have hs1 : s < 1 := by linarith
  have hsq := sq_lt_one_of_mem (show s ∈ Ioo (-1) 1 from ⟨by linarith, hs1⟩)
  have hnum : 0 < 1 - s ^ 2 / 2 := by linarith
  have ha := (le_div_iff₀ hnum).mp (artanh_le_rational hs.le hs9)
  have hmul := mul_le_mul_of_nonneg_left ha (sq_nonneg s)
  unfold comparisonModelKernel comparisonKernel
  apply (div_le_div_iff₀ (pow_pos hs 3)
    (mul_pos (sq_pos_of_pos hs) (Real.artanh_pos ⟨hs, hs1⟩))).mpr
  nlinarith

theorem hasDerivAt_comparisonPrimitive {s : ℝ} (hs : 0 < s) :
    HasDerivAt comparisonPrimitive (comparisonModelKernel s) s := by
  have hden : 2 * s ^ 2 ≠ 0 := by positivity
  have hd := (((hasDerivAt_const s 1).div
    (((hasDerivAt_id s).pow 2).const_mul 2) hden).neg).sub
      ((Real.hasDerivAt_log hs.ne').div_const 2)
  convert! hd using 1
  simp only [id_eq, Pi.pow_apply]
  unfold comparisonModelKernel
  field_simp [hs.ne']
  ring

theorem continuousAt_comparisonModelKernel {s : ℝ} (hs : 0 < s) :
    ContinuousAt comparisonModelKernel s := by
  unfold comparisonModelKernel
  fun_prop (disch := positivity)

theorem integral_comparisonModelKernel {u : ℝ} (hu : 0 < u) (hu9 : u ≤ 9 / 10) :
    (∫ s in u..(9 / 10), comparisonModelKernel s) =
      (1 - u ^ 2 * comparisonC u) / (2 * u ^ 2) := by
  have hpos : ∀ s ∈ uIcc u (9 / 10), 0 < s := by
    intro s hs
    rw [uIcc_of_le hu9] at hs
    exact hu.trans_le hs.1
  have hint : IntervalIntegrable comparisonModelKernel volume u (9 / 10) :=
    ContinuousOn.intervalIntegrable
      (fun s hs => (continuousAt_comparisonModelKernel (hpos s hs)).continuousWithinAt)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hasDerivAt_comparisonPrimitive (hpos s hs)) hint]
  unfold comparisonPrimitive comparisonC
  norm_num
  field_simp [hu.ne']
  ring

theorem comparisonV_lower {u : ℝ} (hu : 0 < u) (hu9 : u ≤ 9 / 10) :
    Real.artanh u / u * (1 - u ^ 2 * comparisonC u) ≤ comparisonV u := by
  have hu1 : u < 1 := by linarith
  have hkernel := intervalIntegrable_comparisonKernel hu hu1
  have hkernel9 : IntervalIntegrable comparisonKernel volume u (9 / 10) := by
    apply hkernel.mono_set
    rw [uIcc_of_le hu9, uIcc_of_le hu1.le]
    exact Icc_subset_Icc le_rfl (by norm_num)
  have hmodel : IntervalIntegrable comparisonModelKernel volume u (9 / 10) := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    rw [uIcc_of_le hu9] at hs
    exact (continuousAt_comparisonModelKernel (hu.trans_le hs.1)).continuousWithinAt
  have hpos : 0 ≤ᵐ[volume.restrict (Ioc u 1)] comparisonKernel := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact comparisonKernel_nonneg (hu.le.trans hs.1.le)
  have hI : (1 - u ^ 2 * comparisonC u) / (2 * u ^ 2) ≤
      ∫ s in u..1, comparisonKernel s := by
    rw [← integral_comparisonModelKernel hu hu9]
    calc
      _ ≤ ∫ s in u..(9 / 10), comparisonKernel s :=
        intervalIntegral.integral_mono_on hu9 hmodel hkernel9
          (fun s hs => comparisonModelKernel_le (hu.trans_le hs.1) hs.2)
      _ ≤ ∫ s in u..1, comparisonKernel s :=
        intervalIntegral.integral_mono_interval le_rfl hu9 (by norm_num) hpos hkernel
  have hm := mul_le_mul_of_nonneg_left hI
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hu.le)
      (Real.artanh_nonneg hu.le))
  convert! hm using 1
  field_simp [hu.ne']

theorem one_sub_comparisonV_le {u : ℝ} (hu0 : 1 / 5 ≤ u) (hu1 : u ≤ 5 / 8) :
    1 - comparisonV u ≤ 5 / 2 * u ^ 2 := by
  have hu : 0 < u := by linarith
  have hu9 : u ≤ 9 / 10 := by linarith
  have hcubic := artanh_cubic_lower hu.le (show u < 1 by linarith)
  have hratio : 1 + u ^ 2 / 3 ≤ Real.artanh u / u := by
    apply (le_div_iff₀ hu).mpr
    nlinarith
  have hprod := mul_le_mul_of_nonneg_right hratio
    (comparisonC_integral_bracket_nonneg hu hu9)
  have hlow := comparisonV_lower hu hu9
  have hQ := mul_le_mul_of_nonneg_left (comparisonC_middle_bound hu0 hu1) (sq_nonneg u)
  nlinarith

def comparisonBias (m : ℝ) : ℝ := m ^ 2 * ell - psi m

theorem comparisonBias_eq (m : ℝ) :
    entropy m = (1 - m ^ 2) * ell + comparisonBias m := by
  unfold comparisonBias entropy
  ring

theorem comparisonBias_bounds {m : ℝ} (hm : |m| ≤ 1) :
    0 ≤ comparisonBias m ∧ comparisonBias m ≤ m ^ 2 * (ell - 1 / 2) := by
  have hlow := half_sq_le_psi hm
  have hupp := psi_le_ell_mul_sq hm
  unfold comparisonBias
  constructor <;> nlinarith

def comparisonLower (A B t : ℝ) : ℝ :=
  A * entropy (Real.exp (-t)) + B * comparisonVTime t

theorem hasDerivAt_entropy_exp_neg {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun z : ℝ => entropy (Real.exp (-z)))
      (Real.exp (-t) * Real.artanh (Real.exp (-t))) t := by
  have hu := Real.exp_pos (-t)
  have hu1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  convert! (hasDerivAt_entropy ⟨by linarith, hu1⟩).comp t (hasDerivAt_id t).neg.exp using 1
  simp only [id_eq, Pi.neg_apply]
  ring

theorem hasDerivAt_comparisonLower (A B : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (comparisonLower A B)
      (A * r (psi (Real.exp (-t))) +
        B * (2 - rDeriv (psi (Real.exp (-t))) * comparisonVTime t)) t := by
  have hu := Real.exp_pos (-t)
  have hu1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  rw [r_psi ⟨by linarith, hu1⟩, rDeriv_psi ⟨hu, hu1⟩]
  exact
    ((hasDerivAt_entropy_exp_neg ht).const_mul A).add ((hasDerivAt_comparisonVTime ht).const_mul B)

theorem comparisonLower_pos {A B t : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (ht : 0 < t) :
    0 < comparisonLower A B t := by
  have hu := Real.exp_pos (-t)
  have hu1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  exact add_pos_of_pos_of_nonneg
    (mul_pos hA (entropy_pos ⟨by linarith, hu1⟩))
    (mul_nonneg hB (comparisonV_nonneg hu.le hu1.le))

theorem tendsto_comparisonLower_zero (A B : ℝ) :
    Tendsto (comparisonLower A B) (𝓝[>] 0) (𝓝 0) := by
  have hu : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[>] 0) (𝓝 1) := by
    have h : Continuous (fun t : ℝ => Real.exp (-t)) := by fun_prop
    simpa using (h.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hh : Tendsto (fun t : ℝ => entropy (Real.exp (-t))) (𝓝[>] 0) (𝓝 0) := by
    convert! (continuous_entropy.tendsto 1).comp hu using 1
    simp
  convert! (tendsto_const_nhds.mul hh).add
    (tendsto_const_nhds.mul tendsto_comparisonVTime_zero) using 1
  simp

theorem comparisonLower_subsolution
    (hLsupport : ∀ x, 0 < x → ∀ y, 0 < y → L x + LDeriv x * (y - x) ≤ L y)
    {A B H t : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hH : H = A * ell + B) (ht : 0 < t) :
    A * r (psi (Real.exp (-t))) +
        B * (2 - rDeriv (psi (Real.exp (-t))) * comparisonVTime t) ≤
      2 * (H - comparisonLower A B t) + A * L (comparisonLower A B t / A) := by
  have hu := Real.exp_pos (-t)
  have hu1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hHu : 0 < entropy (Real.exp (-t)) := entropy_pos ⟨by linarith, hu1⟩
  have hlowpos := comparisonLower_pos hA hB ht
  have htangent := hLsupport _ hHu _ (div_pos hlowpos hA)
  have hscaled : A * L (entropy (Real.exp (-t))) +
      LDeriv (entropy (Real.exp (-t))) * (B * comparisonVTime t) ≤
        A * L (comparisonLower A B t / A) := by
    calc
      _ = A * (L (entropy (Real.exp (-t))) +
          LDeriv (entropy (Real.exp (-t))) *
            (comparisonLower A B t / A - entropy (Real.exp (-t)))) := by
              unfold comparisonLower
              field_simp [hA.ne']
              ring
      _ ≤ _ := mul_le_mul_of_nonneg_left htangent hA.le
  rw [L_entropy ⟨by linarith, hu1⟩, LDeriv_entropy ⟨hu, hu1⟩] at hscaled
  rw [hH]
  unfold comparisonLower entropy at hscaled ⊢
  nlinarith [hscaled]

theorem comparison_rhs_antitone (hLmono : AntitoneOn L (Ioi 0))
    {A : ℝ} (hA : 0 < A) (H : ℝ) :
    AntitoneOn (fun x => 2 * (H - x) + A * L (x / A)) (Ioi 0) := by
  intro x hx y hy hxy
  have hL := hLmono (div_pos hx hA) (div_pos hy hA) ((div_le_div_iff_of_pos_right hA).mpr hxy)
  exact add_le_add (by linarith) (mul_le_mul_of_nonneg_left hL hA.le)

theorem comparisonLower_le_of_differential_inequality
    (hLmono : AntitoneOn L (Ioi 0))
    (hLsupport : ∀ x, 0 < x → ∀ y, 0 < y → L x + LDeriv x * (y - x) ≤ L y)
    {A B H : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hH : H = A * ell + B)
    (h h' : ℝ → ℝ) (hpos : ∀ t, 0 < t → 0 < h t)
    (hderiv : ∀ t, 0 < t → HasDerivAt h (h' t) t)
    (hdiff : ∀ t, 0 < t → 2 * (H - h t) + A * L (h t / A) ≤ h' t)
    (hinit : Tendsto h (𝓝[>] 0) (𝓝 0)) :
    ∀ t, 0 < t → comparisonLower A B t ≤ h t := by
  apply le_of_deriv_le_on_above_of_tendsto
    (fun t ht => hasDerivAt_comparisonLower A B ht) hderiv
    _ (tendsto_comparisonLower_zero A B) hinit
  intro t ht horder
  exact (comparisonLower_subsolution hLsupport hA hB hH ht).trans
    (((comparison_rhs_antitone hLmono hA H) (hpos t ht)
      (comparisonLower_pos hA hB ht) horder).trans (hdiff t ht))

theorem hasDerivAt_psi_exp_neg {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun z : ℝ => psi (Real.exp (-z)))
      (-r (psi (Real.exp (-t)))) t := by
  have hu := Real.exp_pos (-t)
  have hu1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  rw [r_psi ⟨by linarith, hu1⟩]
  convert! (hasDerivAt_psi ⟨by linarith, hu1⟩).comp t (hasDerivAt_id t).neg.exp using 1
  simp only [id_eq, Pi.neg_apply]
  ring

theorem small_information_comparison
    (hrmono : MonotoneOn r (Ico 0 ell))
    (S S' : ℝ → ℝ) {t0 : ℝ} (ht0 : 0 < t0)
    (hderiv : ∀ t, t0 ≤ t → HasDerivAt S (S' t) t)
    (hrange : ∀ t, t0 ≤ t → S t ∈ Ico 0 ell)
    (hdecay : ∀ t, t0 ≤ t → S' t ≤ -r (S t))
    (hstart : S t0 ≤ psi (Real.exp (-t0))) :
    ∀ t, t0 ≤ t → S t ≤ psi (Real.exp (-t)) := by
  intro t htt0
  refine le_of_deriv_le_on_above (a := t0) (b := t)
    (fun z hz => hderiv z hz.1)
    (fun z hz => hasDerivAt_psi_exp_neg (ht0.trans_le hz.1))
    ?_ hstart t ⟨htt0, le_rfl⟩
  intro z hz hcross
  have hz0 : 0 < z := ht0.trans_le hz.1
  have hu := Real.exp_pos (-z)
  have hu1 : Real.exp (-z) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpsi : psi (Real.exp (-z)) ∈ Ico 0 ell :=
    ⟨psi_nonneg _, psi_lt_ell ⟨by linarith, hu1⟩⟩
  exact (hdecay z hz.1).trans (neg_le_neg (hrmono hpsi (hrange z hz.1) hcross))

theorem noiseFlow_comparison_lower_from_dissipation
    (hLmono : AntitoneOn L (Ioi 0))
    (hLsupport : ∀ x, 0 < x → ∀ y, 0 < y → L x + LDeriv x * (y - x) ≤ L y)
    {n : ℕ}
    (hmonoD : ∀ g : Cube n → ℝ, IsInterior g → IsIncreasing g →
      2 * informationDeficit g + meanVariance g * L (entropyAverage g / meanVariance g) ≤
        dissipation g)
    (F : Cube n → ℝ) (hF : IsSignValued F) (hinc : IsIncreasing F)
    (hnc : ∃ x y, F x ≠ F y) :
    ∀ t, 0 < t →
      comparisonLower (1 - (cubeAverage F) ^ 2) (comparisonBias (cubeAverage F)) t ≤
        entropyAverage (noiseFlow F t) := by
  have hm : |cubeAverage F| ≤ 1 :=
    (abs_lt.mpr (cubeAverage_mem_Ioo_of_signValued_nonconstant hF hnc)).le
  have hA : 0 < 1 - (cubeAverage F) ^ 2 :=
    meanVariance_pos_of_signValued_nonconstant hF hnc
  apply comparisonLower_le_of_differential_inequality hLmono hLsupport hA
    (comparisonBias_bounds hm).1 (comparisonBias_eq (cubeAverage F))
    (fun t => entropyAverage (noiseFlow F t)) (fun t => dissipation (noiseFlow F t))
    (fun t ht => entropyAverage_noiseFlow_pos F hF hnc ht)
    (fun t ht => hasDerivAt_entropyAverage_noiseFlow F hF hnc ht)
    _ (tendsto_entropyAverage_noiseFlow_zero_right F hF)
  intro t ht
  simpa only [informationDeficit, meanVariance, cubeAverage_noiseFlow] using
    hmonoD (noiseFlow F t) (isInterior_noiseFlow F hF hnc ht) (isIncreasing_noiseFlow F hinc ht.le)

theorem informationDeficit_noiseFlow_le_comparison_from_dissipation
    (hLmono : AntitoneOn L (Ioi 0))
    (hLsupport : ∀ x, 0 < x → ∀ y, 0 < y → L x + LDeriv x * (y - x) ≤ L y)
    {n : ℕ}
    (hmonoD : ∀ g : Cube n → ℝ, IsInterior g → IsIncreasing g →
      2 * informationDeficit g + meanVariance g * L (entropyAverage g / meanVariance g) ≤
        dissipation g)
    (F : Cube n → ℝ) (hF : IsSignValued F) (hinc : IsIncreasing F)
    (hnc : ∃ x y, F x ≠ F y) {t : ℝ} (ht : 0 < t) :
    informationDeficit (noiseFlow F t) ≤
      (1 - (cubeAverage F) ^ 2) * psi (Real.exp (-t)) +
        comparisonBias (cubeAverage F) * (1 - comparisonVTime t) := by
  have hlow := noiseFlow_comparison_lower_from_dissipation
    hLmono hLsupport hmonoD F hF hinc hnc t ht
  calc
    informationDeficit (noiseFlow F t) =
        entropy (cubeAverage F) - entropyAverage (noiseFlow F t) := by
      simp only [informationDeficit, cubeAverage_noiseFlow]
    _ ≤ entropy (cubeAverage F) -
        comparisonLower (1 - (cubeAverage F) ^ 2) (comparisonBias (cubeAverage F)) t :=
      sub_le_sub_left hlow _
    _ = _ := by
      rw [comparisonBias_eq (cubeAverage F)]
      unfold comparisonLower entropy
      ring

theorem informationDeficit_noiseFlow_le_psi_large_from_dissipation
    (hLmono : AntitoneOn L (Ioi 0))
    (hLsupport : ∀ x, 0 < x → ∀ y, 0 < y → L x + LDeriv x * (y - x) ≤ L y)
    {n : ℕ}
    (hmonoD : ∀ g : Cube n → ℝ, IsInterior g → IsIncreasing g →
      2 * informationDeficit g + meanVariance g * L (entropyAverage g / meanVariance g) ≤
        dissipation g)
    (F : Cube n → ℝ) (hF : IsSignValued F) (hinc : IsIncreasing F)
    (hnc : ∃ x y, F x ≠ F y) {t : ℝ} (ht : 0 < t)
    (hu0 : 1 / 5 ≤ Real.exp (-t)) :
    informationDeficit (noiseFlow F t) ≤ psi (Real.exp (-t)) := by
  have hu := Real.exp_pos (-t)
  have hu1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hm : |cubeAverage F| ≤ 1 :=
    (abs_lt.mpr (cubeAverage_mem_Ioo_of_signValued_nonconstant hF hnc)).le
  have hB := comparisonBias_bounds hm
  have hP := half_sq_le_psi (show |Real.exp (-t)| ≤ 1 by rw [abs_of_pos hu]; exact hu1.le)
  have hS := informationDeficit_noiseFlow_le_comparison_from_dissipation
    hLmono hLsupport hmonoD F hF hinc hnc ht
  by_cases hlarge : 5 / 8 ≤ Real.exp (-t)
  · exact comparison_large_regime (cubeAverage F) (Real.exp (-t))
      (comparisonBias (cubeAverage F)) (psi (Real.exp (-t)))
      (informationDeficit (noiseFlow F t)) (comparisonVTime t)
      hB.1 hB.2 hP hS hlarge (comparisonV_nonneg hu.le hu1.le)
  · apply comparison_middle_regime (cubeAverage F) (Real.exp (-t))
      (comparisonBias (cubeAverage F)) (psi (Real.exp (-t)))
      (informationDeficit (noiseFlow F t)) (comparisonVTime t)
      hB.1 hB.2 hP hS
    exact one_sub_comparisonV_le hu0 (le_of_not_ge hlarge)

theorem dissipation_nonneg {n : ℕ} (g : Cube n → ℝ) (hg : IsInterior g) :
    0 ≤ dissipation g := by
  induction n with
  | zero => simp [dissipation]
  | succ n ih =>
      rw [dissipation_split]
      exact add_nonneg
        (div_nonneg (add_nonneg (ih _ (hg.restrict true)) (ih _ (hg.restrict false)))
          (by norm_num))
        (cubeAverage_nonneg fun x => pairDissipation_nonneg _ _ (hg.pairDomain x))

theorem antitone_informationDeficit_noiseFlow {n : ℕ}
    (F : Cube n → ℝ) (hF : IsSignValued F) (hnc : ∃ x y, F x ≠ F y) :
    AntitoneOn (fun t => informationDeficit (noiseFlow F t)) (Ioi 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
    (continuous_informationDeficit_noiseFlow F).continuousOn
  · intro t ht
    have ht' : 0 < t := interior_subset ht
    exact (hasDerivAt_informationDeficit_noiseFlow F hF hnc ht').hasDerivWithinAt
  · intro t ht
    have ht' : 0 < t := interior_subset ht
    exact neg_nonpos.mpr (dissipation_nonneg _ (isInterior_noiseFlow F hF hnc ht'))

private theorem exp_neg_log_five : Real.exp (-Real.log 5) = (1 / 5 : ℝ) := by
  rw [Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

theorem informationDeficit_noiseFlow_le_psi_from_dissipation
    (hLmono : AntitoneOn L (Ioi 0))
    (hLsupport : ∀ x, 0 < x → ∀ y, 0 < y → L x + LDeriv x * (y - x) ≤ L y)
    (hrmono : MonotoneOn r (Ico 0 ell))
    {n : ℕ}
    (hmonoD : ∀ g : Cube n → ℝ, IsInterior g → IsIncreasing g →
      2 * informationDeficit g + meanVariance g * L (entropyAverage g / meanVariance g) ≤
        dissipation g)
    (hsmallD : ∀ g : Cube n → ℝ, IsInterior g → informationDeficit g ≤ s0 →
      r (informationDeficit g) ≤ dissipation g)
    (F : Cube n → ℝ) (hF : IsSignValued F) (hinc : IsIncreasing F)
    (hnc : ∃ x y, F x ≠ F y) {t : ℝ} (ht : 0 < t) :
    informationDeficit (noiseFlow F t) ≤ psi (Real.exp (-t)) := by
  have hlarge (z : ℝ) (hz : 0 < z) (huz : 1 / 5 ≤ Real.exp (-z)) :
      informationDeficit (noiseFlow F z) ≤ psi (Real.exp (-z)) :=
    informationDeficit_noiseFlow_le_psi_large_from_dissipation
      hLmono hLsupport hmonoD F hF hinc hnc hz huz
  by_cases hu0 : 1 / 5 ≤ Real.exp (-t)
  · exact hlarge t ht hu0
  · have ht0 : 0 < Real.log 5 := Real.log_pos (by norm_num)
    have hstart : informationDeficit (noiseFlow F (Real.log 5)) ≤ psi (Real.exp (-Real.log 5)) :=
      hlarge (Real.log 5) ht0 (by rw [exp_neg_log_five])
    have hstart0 : informationDeficit (noiseFlow F (Real.log 5)) ≤ s0 := by
      simpa only [exp_neg_log_five, s0] using hstart
    have hSsmall : ∀ z, Real.log 5 ≤ z → informationDeficit (noiseFlow F z) ≤ s0 := by
      intro z hz
      exact ((antitone_informationDeficit_noiseFlow F hF hnc) ht0 (ht0.trans_le hz) hz).trans hstart0
    have hSrange : ∀ z, Real.log 5 ≤ z → informationDeficit (noiseFlow F z) ∈ Ico 0 ell := by
      intro z hz
      refine ⟨informationDeficit_nonneg (isInterior_noiseFlow F hF hnc (ht0.trans_le hz)), ?_⟩
      exact (hSsmall z hz).trans_lt (psi_lt_ell (by norm_num : (1 / 5 : ℝ) ∈ Ioo (-1) 1))
    have hbound := small_information_comparison hrmono
      (fun z => informationDeficit (noiseFlow F z)) (fun z => -dissipation (noiseFlow F z)) ht0
      (fun z hz => hasDerivAt_informationDeficit_noiseFlow F hF hnc (ht0.trans_le hz))
      hSrange
      (fun z hz => neg_le_neg (hsmallD _ (isInterior_noiseFlow F hF hnc (ht0.trans_le hz))
        (hSsmall z hz))) hstart
    apply hbound t
    have hcomp : Real.exp (-t) ≤ Real.exp (-Real.log 5) := by
      rw [exp_neg_log_five]
      exact le_of_not_ge hu0
    have hcomp' := Real.exp_le_exp.mp hcomp
    linarith

theorem informationDeficit_noise_le_psi_from_dissipation
    (hLmono : AntitoneOn L (Ioi 0))
    (hLsupport : ∀ x, 0 < x → ∀ y, 0 < y → L x + LDeriv x * (y - x) ≤ L y)
    (hrmono : MonotoneOn r (Ico 0 ell))
    {n : ℕ}
    (hmonoD : ∀ g : Cube n → ℝ, IsInterior g → IsIncreasing g →
      2 * informationDeficit g + meanVariance g * L (entropyAverage g / meanVariance g) ≤
        dissipation g)
    (hsmallD : ∀ g : Cube n → ℝ, IsInterior g → informationDeficit g ≤ s0 →
      r (informationDeficit g) ≤ dissipation g)
    (F : Cube n → ℝ) (hF : IsSignValued F) (hinc : IsIncreasing F)
    (hnc : ∃ x y, F x ≠ F y) (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    informationDeficit (noiseOperator u F) ≤ psi u := by
  have ht : 0 < -Real.log u := neg_pos.mpr (Real.log_neg hu0 hu1)
  simpa only [noiseFlow, neg_neg, Real.exp_log hu0] using
    informationDeficit_noiseFlow_le_psi_from_dissipation hLmono hLsupport hrmono hmonoD hsmallD
      F hF hinc hnc ht

theorem informationDeficit_noise_le_psi_from_sharp_dissipation
    {n : ℕ}
    (hmonoD : ∀ g : Cube n → ℝ, IsInterior g → IsIncreasing g →
      2 * informationDeficit g + meanVariance g * L (entropyAverage g / meanVariance g) ≤
        dissipation g)
    (hsmallD : ∀ g : Cube n → ℝ, IsInterior g → informationDeficit g ≤ s0 →
      r (informationDeficit g) ≤ dissipation g)
    (F : Cube n → ℝ) (hF : IsSignValued F) (hinc : IsIncreasing F)
    (hnc : ∃ x y, F x ≠ F y) (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    informationDeficit (noiseOperator u F) ≤ psi u := by
  have hrmono : MonotoneOn r (Ico 0 ell) := by
    intro x hx y hy hxy
    have hgap := monotoneOn_rGap hx hy hxy
    unfold rGap at hgap
    linarith
  exact informationDeficit_noise_le_psi_from_dissipation
    antitoneOn_L L_support hrmono hmonoD hsmallD F hF hinc hnc u hu0 hu1

theorem informationDeficit_noise_le_psi_of_increasing
    {n : ℕ} (F : Cube n → ℝ) (hF : IsSignValued F) (hinc : IsIncreasing F)
    (hnc : ∃ x y, F x ≠ F y) (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    informationDeficit (noiseOperator u F) ≤ psi u :=
  informationDeficit_noise_le_psi_from_sharp_dissipation
    (fun g hg hmono => monotone_dissipation g hg hmono)
    (fun g hg hS => small_information_dissipation g hg hS)
    F hF hinc hnc u hu0 hu1

end LeanBlast.CourtadeKumar

end

end OAI
