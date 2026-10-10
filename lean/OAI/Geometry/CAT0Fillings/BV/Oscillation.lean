import Mathlib
import OAI.Geometry.CAT0Fillings.BV.Poincare

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.JointBV

lemma abs_setAverage_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs0 : 0 < μ.real s) (hsf : μ s ≠ ∞)
    {f : α → ℝ} (hf : IntegrableOn f s μ) (c : ℝ) :
    |(⨍ z in s, f z ∂μ) - c| ≤ (μ.real s)⁻¹ * ∫ z in s, |f z - c| ∂μ := by
  have hs : μ s ≠ 0 := by
    intro h
    simp [measureReal_def, h] at hs0
  have : IsFiniteMeasure (μ.restrict s) := ⟨by simpa using hsf.lt_top⟩
  have hi : IntegrableOn (fun z => f z - c) s μ := hf.sub (integrable_const c)
  have he : (⨍ z in s, f z ∂μ) - c =
      (μ.real s)⁻¹ * ∫ z in s, f z - c ∂μ := by
    rw [integral_sub hf (integrable_const c), integral_const]
    simp only [Measure.restrict_apply_univ, smul_eq_mul, measureReal_def] at *
    rw [setAverage_eq]
    simp only [smul_eq_mul, measureReal_def]
    field_simp
  rw [he, abs_mul, abs_of_nonneg (inv_nonneg.mpr hs0.le)]
  exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (inv_nonneg.mpr hs0.le)

lemma abs_setAverage_sub_le_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s t : Set α} (hs : MeasurableSet s) (hst : s ⊆ t)
    (hs0 : 0 < μ.real s) (htf : μ t ≠ ∞)
    {f : α → ℝ} (hf : IntegrableOn f t μ) (c : ℝ) :
    |(⨍ z in s, f z ∂μ) - c| ≤ (μ.real s)⁻¹ * ∫ z in t, |f z - c| ∂μ := by
  have hsf : μ s ≠ ∞ := ne_of_lt ((measure_mono hst).trans_lt htf.lt_top)
  have : IsFiniteMeasure (μ.restrict t) := ⟨by simpa using htf.lt_top⟩
  apply (abs_setAverage_sub_le hs0 hsf (hf.mono_set hst) c).trans
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hs0.le)
  simpa only [Measure.restrict_restrict hs, inter_eq_left.mpr hst, Pi.sub_apply] using
    setIntegral_le_integral (s := s) (hf.sub (integrable_const c)).abs
      (ae_of_all _ fun point => abs_nonneg (f point - c))

section Euclidean
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]

omit [BorelSpace E] in
lemma haar_closedBall_pos {x : E} {r : ℝ} (hr : 0 < r) :
    0 < μ.real (closedBall x r) := by
  apply ENNReal.toReal_pos
  · exact ne_of_gt ((measure_ball_pos μ x hr).trans_le (measure_mono ball_subset_closedBall))
  · exact measure_closedBall_lt_top.ne

lemma haar_closedBall_scale (x y : E) {r : ℝ} (hr : 0 < r) (a : ℝ) (ha : 0 ≤ a) :
    μ.real (closedBall x (a * r)) = a ^ Module.finrank ℝ E * μ.real (closedBall y r) := by
  rw [Measure.addHaar_real_closedBall _ _ (mul_nonneg ha hr.le),
    Measure.addHaar_real_closedBall _ _ hr.le, mul_pow, mul_assoc]

def LocalMeanBound (f : E → ℝ) (A : ℝ) (x : E) (R : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → r ≤ R →
    (∫ z in closedBall x r, |f z - (⨍ w in closedBall x r, f w ∂μ)| ∂μ) ≤
      A * r * μ.real (closedBall x r)

lemma average_half_bound {f : E → ℝ} (hf : LocallyIntegrable f μ)
    {A : ℝ} {x : E} {R r : ℝ} (hA : LocalMeanBound (μ := μ) f A x R)
    (hr : 0 < r) (hrR : r ≤ R) :
    |(⨍ z in closedBall x (r / 2), f z ∂μ) -
      (⨍ z in closedBall x r, f z ∂μ)| ≤
      (2 : ℝ) ^ Module.finrank ℝ E * A * r := by
  have hrh : 0 < r / 2 := by positivity
  have hs0 := haar_closedBall_pos (μ := μ) (x := x) hrh
  have hI := hf.integrableOn_isCompact (isCompact_closedBall x r)
  have hsub : closedBall x (r / 2) ⊆ closedBall x r :=
    closedBall_subset_closedBall (by linarith)
  apply (abs_setAverage_sub_le_integral isClosed_closedBall.measurableSet hsub
    hs0 measure_closedBall_lt_top.ne hI _).trans
  have he : μ.real (closedBall x r) =
      (2 : ℝ) ^ Module.finrank ℝ E * μ.real (closedBall x (r / 2)) := by
    have hh := haar_closedBall_scale (μ := μ) x x hrh 2 (by norm_num)
    rwa [show 2 * (r / 2) = r by ring] at hh
  calc
    _ ≤ (μ.real (closedBall x (r / 2)))⁻¹ * (A * r * μ.real (closedBall x r)) :=
      mul_le_mul_of_nonneg_left (hA r hr hrR) (inv_nonneg.mpr hs0.le)
    _ = (2 : ℝ) ^ Module.finrank ℝ E * A * r := by rw [he]; field_simp

lemma point_average_bound {f : E → ℝ} (hf : LocallyIntegrable f μ)
    {A : ℝ} {x : E} {R r : ℝ} (hA : LocalMeanBound (μ := μ) f A x R)
    (hr : 0 < r) (hrR : r ≤ R)
    (hlim : Tendsto (fun n : ℕ => ⨍ z in closedBall x (r * (1 / 2 : ℝ)^n), f z ∂μ)
      atTop (𝓝 (f x))) :
    |f x - (⨍ z in closedBall x r, f z ∂μ)| ≤
      2 * (2 : ℝ)^Module.finrank ℝ E * A * r := by
  let a (n : ℕ) := ⨍ z in closedBall x (r * (1 / 2 : ℝ)^n), f z ∂μ
  let D := (2 : ℝ)^Module.finrank ℝ E * A * r
  have hstep (n : ℕ) : dist (a n) (a (n+1)) ≤ D * (1 / 2 : ℝ)^n := by
    have hrn : 0 < r * (1 / 2 : ℝ)^n := by positivity
    have hrnR : r * (1 / 2 : ℝ)^n ≤ R := by
      apply le_trans _ hrR
      exact mul_le_of_le_one_right hr.le (pow_le_one₀ (by norm_num) (by norm_num))
    have hh := average_half_bound hf hA hrn hrnR
    have he : r * (1 / 2 : ℝ)^n / 2 = r * (1 / 2 : ℝ)^(n+1) := by
      rw [pow_succ]; ring
    rw [he] at hh
    change |a n - a (n+1)| ≤ _
    rw [abs_sub_comm]
    convert hh using 1
    dsimp [a, D]
    ring
  have hg : Summable (fun n : ℕ => (1 / 2 : ℝ)^n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hh := dist_le_tsum_of_dist_le_of_tendsto₀ _ hstep (hg.mul_left D) hlim
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1 / 2 : ℝ) < 1)] at hh
  norm_num only [one_div, inv_inv] at hh
  simpa only [a, pow_zero, mul_one, Real.dist_eq, abs_sub_comm, D, mul_comm, mul_left_comm,
    mul_assoc] using hh

lemma average_neighbor_bound {f : E → ℝ} (hf : LocallyIntegrable f μ)
    {A : ℝ} {x y : E} {R r : ℝ} (hA : LocalMeanBound (μ := μ) f A x R)
    (hr : 0 < r) (hrR : 2 * r ≤ R) (hxy : dist y x ≤ r) :
    |(⨍ z in closedBall y r, f z ∂μ) -
      (⨍ z in closedBall x (2 * r), f z ∂μ)| ≤
      2 * (2 : ℝ) ^ Module.finrank ℝ E * A * r := by
  have hs0 := haar_closedBall_pos (μ := μ) (x := y) hr
  have hI := hf.integrableOn_isCompact (isCompact_closedBall x (2*r))
  have hsub : closedBall y r ⊆ closedBall x (2*r) := by
    intro z hz
    change dist z x ≤ 2 * r
    have hh := dist_triangle z y x
    have hz' : dist z y ≤ r := hz
    linarith
  apply (abs_setAverage_sub_le_integral isClosed_closedBall.measurableSet hsub
    hs0 measure_closedBall_lt_top.ne hI _).trans
  have he := haar_closedBall_scale (μ := μ) x y hr 2 (by norm_num)
  calc
    _ ≤ (μ.real (closedBall y r))⁻¹ * (A * (2*r) * μ.real (closedBall x (2*r))) :=
      mul_le_mul_of_nonneg_left (hA (2*r) (by positivity) hrR) (inv_nonneg.mpr hs0.le)
    _ = 2 * (2 : ℝ)^Module.finrank ℝ E * A * r := by
      rw [he]; field_simp

lemma ae_ballAverage_tendsto {f : E → ℝ} (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun r : ℝ => ⨍ z in closedBall x r, f z ∂μ)
      (𝓝[>] 0) (𝓝 (f x)) := by
  filter_upwards [(Besicovitch.vitaliFamily μ).ae_tendsto_average hf] with x hx
  exact hx.comp (Besicovitch.tendsto_filterAt μ x)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
lemma dyadic_closedBall_average_tendsto {f : E → ℝ} {x : E}
    (hx : Tendsto (fun r : ℝ => ⨍ z in closedBall x r, f z ∂μ)
      (𝓝[>] 0) (𝓝 (f x))) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n : ℕ => ⨍ z in closedBall x (r * (1 / 2 : ℝ)^n), f z ∂μ)
      atTop (𝓝 (f x)) := by
  apply hx.comp
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using (tendsto_const_nhds (x := r)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (1/2 : ℝ) < 1))
  · exact Eventually.of_forall fun n => by simp only [mem_Ioi]; positivity

lemma abs_sub_le_of_localMeanBound {f : E → ℝ} (hf : LocallyIntegrable f μ)
    {A R : ℝ} {x y : E}
    (hAx : LocalMeanBound (μ := μ) f A x R)
    (hAy : LocalMeanBound (μ := μ) f A y R)
    (hx : Tendsto (fun r : ℝ => ⨍ z in closedBall x r, f z ∂μ) (𝓝[>] 0) (𝓝 (f x)))
    (hy : Tendsto (fun r : ℝ => ⨍ z in closedBall y r, f z ∂μ) (𝓝[>] 0) (𝓝 (f y)))
    (hxy : 2 * dist x y ≤ R) :
    |f x - f y| ≤ 8 * (2 : ℝ)^Module.finrank ℝ E * A * dist x y := by
  by_cases he : x = y
  · simp [he]
  have hr : 0 < dist x y := dist_pos.mpr he
  have hrR : dist x y ≤ R := by linarith
  have hx' := point_average_bound hf hAx (show 0 < 2 * dist x y by positivity) hxy
    (dyadic_closedBall_average_tendsto hx (by positivity))
  have hy' := point_average_bound hf hAy hr hrR (dyadic_closedBall_average_tendsto hy hr)
  have hc := average_neighbor_bound hf hAx hr hxy (by rw [dist_comm])
  have htri : |f x - f y| ≤
      |f x - (⨍ z in closedBall x (2 * dist x y), f z ∂μ)| +
      |(⨍ z in closedBall y (dist x y), f z ∂μ) -
        (⨍ z in closedBall x (2 * dist x y), f z ∂μ)| +
      |f y - (⨍ z in closedBall y (dist x y), f z ∂μ)| := by
    simpa only [Real.dist_eq, abs_sub_comm] using
      dist_triangle4 (f x) (⨍ z in closedBall x (2 * dist x y), f z ∂μ)
        (⨍ z in closedBall y (dist x y), f z ∂μ) (f y)
  linarith

end Euclidean
end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.JointBV

lemma integral_abs_le_of_ae_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {F : ℕ → α → ℝ} (hf : Integrable f μ) (hF : ∀ j, Integrable (F j) μ)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun j => F j x) atTop (𝓝 (f x))) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᶠ j in atTop, (∫ x, |F j x| ∂μ) ≤ C) : (∫ x, |f x| ∂μ) ≤ C := by
  have hl' : ∀ᵐ x ∂μ, Tendsto (fun j => ENNReal.ofReal |F j x|) atTop
      (𝓝 (ENNReal.ofReal |f x|)) := hl.mono fun x hx => ENNReal.continuous_ofReal.continuousAt.tendsto.comp hx.abs
  have hfat : (∫⁻ x, ENNReal.ofReal |f x| ∂μ) ≤
      liminf (fun j => ∫⁻ x, ENNReal.ofReal |F j x| ∂μ) atTop := by
    calc _ = ∫⁻ x, liminf (fun j => ENNReal.ofReal |F j x|) atTop ∂μ :=
        lintegral_congr_ae (hl'.mono fun _ hx => hx.liminf_eq.symm)
      _ ≤ _ := lintegral_liminf_le' (fun j => (hF j).abs.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have hu : liminf (fun j => ∫⁻ x, ENNReal.ofReal |F j x| ∂μ) atTop ≤ ENNReal.ofReal C := by
    apply liminf_le_of_frequently_le'
    apply Filter.Eventually.frequently
    filter_upwards [hbound] with j hj
    rw [←ofReal_integral_eq_lintegral_ofReal (hF j).abs (ae_of_all _ fun x => abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hj
  rw [←ofReal_integral_eq_lintegral_ofReal hf.abs (ae_of_all _ fun x => abs_nonneg _)] at hfat
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp (hfat.trans hu)

lemma pair_integral_le_oscillation {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : Integrable f μ) (c : ℝ) :
    (∫ p : α × α, |f p.1-f p.2| ∂μ.prod μ) ≤ 2*μ.real univ*(∫ x, |f x-c| ∂μ) := by
  have hi := (hf.sub (integrable_const c)).abs
  have hp := (hf.comp_fst μ).sub (hf.comp_snd μ)
  have hm := integral_mono hp.abs ((hi.comp_fst μ).add (hi.comp_snd μ)) (fun p => by
    have ht := abs_sub_le (f p.1) c (f p.2)
    rwa [abs_sub_comm c (f p.2)] at ht)
  simp only [Pi.add_apply,Pi.sub_apply] at hm hi hp
  rw [integral_add (hi.comp_fst μ) (hi.comp_snd μ),integral_prod _ (hi.comp_fst μ),
    integral_prod _ (hi.comp_snd μ)] at hm
  simp only [integral_const,smul_eq_mul,integral_const_mul] at hm
  exact hm.trans_eq (by ring)

lemma oscillation_le_pair_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (hμ : 0 < μ.real univ) {f : α → ℝ} (hf : Integrable f μ) :
    (∫ x, |f x-(⨍ y, f y ∂μ)| ∂μ) ≤
      (μ.real univ)⁻¹*(∫ p : α × α, |f p.1-f p.2| ∂μ.prod μ) := by
  have hp := ((hf.comp_fst μ).sub (hf.comp_snd μ)).abs
  have hpoint (x : α) : |f x-(⨍ y, f y ∂μ)| ≤ (μ.real univ)⁻¹*∫ y, |f x-f y| ∂μ := by
    have hh := abs_setAverage_sub_le (s := univ) hμ (measure_ne_top _ _) (by simpa using hf) (f x)
    simpa [abs_sub_comm] using hh
  have hm := integral_mono (hf.sub (integrable_const _)).abs
    (hp.integral_prod_left.const_mul ((μ.real univ)⁻¹)) hpoint
  rw [integral_const_mul,←integral_prod _ hp] at hm
  exact hm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

theorem ball_poincare_of_smooth_approx {f : E → ℝ} (hf : LocallyIntegrable f μ)
    (F : ℕ → E → ℝ) (F' : ℕ → E → E →L[ℝ] ℝ)
    (hF : ∀ j x, HasFDerivAt (F j) (F' j x) x) (hF' : ∀ j, Continuous (F' j))
    (hl : ∀ᵐ x ∂μ, Tendsto (fun j => F j x) atTop (𝓝 (f x)))
    (a : E) {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    (hgrad : ∀ᶠ j in atTop, (∫ x in closedBall a r, ‖F' j x‖ ∂μ) ≤ B) :
    (∫ x in closedBall a r, |f x-(⨍ y in closedBall a r, f y ∂μ)| ∂μ) ≤
      4*(2:ℝ)^Module.finrank ℝ E*r*B := by
  let Q := closedBall a r
  let m := μ.restrict Q
  have hQ : IsCompact Q := isCompact_closedBall a r
  have hm : 0 < m.real univ := by simpa [m,measureReal_restrict_apply_univ] using
    (haar_closedBall_pos (μ := μ) (x := a) hr)
  have : IsFiniteMeasure m := ⟨by simpa [m] using hQ.measure_lt_top⟩
  have hfi : Integrable f m := hf.integrableOn_isCompact hQ
  have hFi (j : ℕ) : Integrable (F j) m := ContinuousOn.integrableOn_compact hQ
    (continuous_iff_continuousAt.mpr (fun x => (hF j x).continuousAt)).continuousOn
  have hlm : ∀ᵐ x ∂m, Tendsto (fun j => F j x) atTop (𝓝 (f x)) := ae_restrict_of_ae hl
  have hlp : ∀ᵐ p : E × E ∂m.prod m,
      Tendsto (fun j => F j p.1-F j p.2) atTop (𝓝 (f p.1-f p.2)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hlm,Measure.quasiMeasurePreserving_snd.ae hlm]
      with p h1 h2 using h1.sub h2
  have hpair : (∫ p : E × E, |f p.1-f p.2| ∂m.prod m) ≤
      m.real univ*(4*(2:ℝ)^Module.finrank ℝ E*r*B) := by
    apply integral_abs_le_of_ae_tendsto ((hfi.comp_fst m).sub (hfi.comp_snd m))
      (fun j => ((hFi j).comp_fst m).sub ((hFi j).comp_snd m)) hlp (by positivity)
    filter_upwards [hgrad] with j hj
    have hp := pair_integral_le_oscillation (hFi j) (⨍ y, F j y ∂m)
    have hs := smooth_ball_poincare (μ := μ) (hF j) (hF' j) a hr
    have hc : 0 ≤ 2*(2:ℝ)^Module.finrank ℝ E*r := by positivity
    have hbound := hs.trans (mul_le_mul_of_nonneg_left hj hc)
    change (∫ x, |F j x-(⨍ y, F j y ∂m)| ∂m) ≤ _ at hbound
    exact hp.trans ((mul_le_mul_of_nonneg_left hbound (by positivity)).trans_eq (by ring))
  have ho := oscillation_le_pair_integral hm hfi
  change (∫ x, |f x-(⨍ y, f y ∂m)| ∂m) ≤ _
  apply (ho.trans (mul_le_mul_of_nonneg_left hpair (inv_nonneg.mpr hm.le))).trans_eq
  rw [←mul_assoc,inv_mul_cancel₀ hm.ne',one_mul]

end CAT0Fillings.JointBV
end

end OAI
