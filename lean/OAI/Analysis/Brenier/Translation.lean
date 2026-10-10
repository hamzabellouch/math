import OAI.Analysis.Brenier.Difference

namespace OAI

noncomputable section

open MeasureTheory Set

namespace Problem358

/-- Integrating a measure-preserving increment over a common core leaves only boundary terms. -/
theorem integral_increment_eq_boundary {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → X} (hf : MeasurePreserving f μ μ)
    (he : MeasurableEmbedding f) {K A : Set X} (hA : MeasurableSet A)
    (hAK : A ⊆ K) (hBK : f '' A ⊆ K) {g : X → ℝ} (hg : IntegrableOn g K μ) :
    (∫ x in A, (g (f x) - g x) ∂μ) =
      (∫ x in K \ A, g x ∂μ) - ∫ x in K \ (f '' A), g x ∂μ := by
  have hgB : IntegrableOn g (f '' A) μ := hg.mono_set hBK
  have hgf : IntegrableOn (fun x => g (f x)) A μ :=
    ((hf.restrict_image_emb he A).integrable_comp hgB.aestronglyMeasurable).mpr hgB
  rw [integral_sub hgf (hg.mono_set hAK),
    ← hf.setIntegral_image_emb he g A,
    setIntegral_sdiff hA hg hAK,
    setIntegral_sdiff (he.measurableSet_image.mpr hA) hg hBK]
  ring

/-- A bounded function has a small mean increment whenever the common core loses little mass. -/
theorem abs_integral_increment_le_boundary {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → X} (hf : MeasurePreserving f μ μ)
    (he : MeasurableEmbedding f) {K A : Set X} (hKfin : μ K ≠ ⊤)
    (hA : MeasurableSet A) (hAK : A ⊆ K) (hBK : f '' A ⊆ K)
    {g : X → ℝ} (hg : IntegrableOn g K μ) {L : ℝ}
    (hbound : ∀ x ∈ K, |g x| ≤ L) :
    |∫ x in A, (g (f x) - g x) ∂μ| ≤ 2 * L * μ.real (K \ A) := by
  have hAB : μ (f '' A) = μ A := by
    simpa only [Set.preimage_image_eq _ he.injective] using
      (hf.measure_preimage_emb he (f '' A)).symm
  have hdiff : μ.real (K \ (f '' A)) = μ.real (K \ A) := by
    rw [measureReal_sdiff hBK (he.measurableSet_image.mpr hA) hKfin,
      measureReal_sdiff hAK hA hKfin, measureReal_def μ (f '' A), hAB]
    rfl
  have hKA : μ (K \ A) < ⊤ :=
    lt_of_le_of_lt (measure_mono sdiff_subset) (lt_top_iff_ne_top.mpr hKfin)
  have hKB : μ (K \ (f '' A)) < ⊤ :=
    lt_of_le_of_lt (measure_mono sdiff_subset) (lt_top_iff_ne_top.mpr hKfin)
  have hbA : |∫ x in K \ A, g x ∂μ| ≤ L * μ.real (K \ A) := by
    simpa only [Real.norm_eq_abs] using
      norm_setIntegral_le_of_norm_le_const (f := g) (C := L) hKA (fun x hx => by
        simpa only [Real.norm_eq_abs] using hbound x hx.1)
  have hbB : |∫ x in K \ (f '' A), g x ∂μ| ≤ L * μ.real (K \ A) := by
    rw [← hdiff]
    simpa only [Real.norm_eq_abs] using
      norm_setIntegral_le_of_norm_le_const (f := g) (C := L) hKB (fun x hx => by
        simpa only [Real.norm_eq_abs] using hbound x hx.1)
  rw [integral_increment_eq_boundary hf he hA hAK hBK hg]
  exact (abs_sub _ _).trans (by linarith)

/-- A one-sided bounded error inherits an integrated square bound from boundary mass. -/
theorem integral_error_sq_le_boundary {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → X} (hf : MeasurePreserving f μ μ)
    (he : MeasurableEmbedding f) {K A : Set X} (hKfin : μ K ≠ ⊤)
    (hA : MeasurableSet A) (hAK : A ⊆ K) (hBK : f '' A ⊆ K)
    {g δ : X → ℝ} (hg : IntegrableOn g K μ)
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ x ∈ K, |g x| ≤ L)
    (hδint : IntegrableOn (fun x => δ x ^ 2) A μ)
    (hδ : ∀ᵐ x ∂μ.restrict A,
      0 ≤ δ x ∧ δ x ≤ g (f x) - g x ∧ g (f x) - g x ≤ 2 * L) :
    (∫ x in A, δ x ^ 2 ∂μ) ≤ 4 * L ^ 2 * μ.real (K \ A) := by
  have hgB : IntegrableOn g (f '' A) μ := hg.mono_set hBK
  have hgf : IntegrableOn (fun x => g (f x)) A μ :=
    ((hf.restrict_image_emb he A).integrable_comp hgB.aestronglyMeasurable).mpr hgB
  have hinc := hgf.sub (hg.mono_set hAK)
  have hpoint : (fun x => δ x ^ 2) ≤ᵐ[μ.restrict A]
      (fun x => (2 * L) * (g (f x) - g x)) := by
    filter_upwards [hδ] with x hx
    have hδL : δ x ≤ 2 * L := hx.2.1.trans hx.2.2
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hδL),
      mul_nonneg (show 0 ≤ 2 * L by positivity) (sub_nonneg.mpr hx.2.1)]
  have hi := integral_mono_ae hδint (hinc.const_mul (2 * L)) hpoint
  rw [integral_const_mul] at hi
  have hb := abs_integral_increment_le_boundary hf he hKfin hA hAK hBK hg hbound
  have hu := le_trans (le_abs_self _) hb
  calc
    (∫ x in A, δ x ^ 2 ∂μ) ≤
        2 * L * (∫ x in A, (g (f x) - g x) ∂μ) := hi
    _ ≤ 2 * L * (2 * L * μ.real (K \ A)) :=
      mul_le_mul_of_nonneg_left hu (by positivity)
    _ = _ := by ring

end Problem358

namespace Problem358

/-- Translation cancellation on a one-dimensional slice. -/
theorem slice_translation_identity {g : ℝ → ℝ} {a b h : ℝ}
    (hh : 0 ≤ h) (hhab : h ≤ b - a)
    (hg : IntervalIntegrable g volume a b) :
    (∫ t in a..b-h, (g (t+h) - g t)) =
      (∫ t in b-h..b, g t) - ∫ t in a..a+h, g t := by
  have hshift : IntervalIntegrable (fun t => g (t+h)) volume a (b-h) :=
    (hg.comp_add_right h).mono_set (by grind [uIcc])
  have hshort : IntervalIntegrable g volume a (b-h) :=
    hg.mono_set (by grind [uIcc])
  rw [intervalIntegral.integral_sub hshift hshort,
    intervalIntegral.integral_comp_add_right]
  simp only [sub_add_cancel]
  exact intervalIntegral.integral_interval_sub_interval_comm'
    (hg.mono_set (by grind [uIcc])) hshort
    (hg.mono_set (by grind [uIcc]))

/-- Bounded derivatives have shift discrepancy at most twice the boundary strip size. -/
theorem slice_translation_le {g : ℝ → ℝ} {a b h L : ℝ}
    (hh : 0 ≤ h) (hhab : h ≤ b-a)
    (hg : IntervalIntegrable g volume a b)
    (hbound : ∀ t ∈ Icc a b, |g t| ≤ L) :
    (∫ t in a..b-h, (g (t+h) - g t)) ≤ 2*L*h := by
  rw [slice_translation_identity hh hhab hg]
  have hupper : (∫ t in b-h..b, g t) ≤ h*L := by
    calc
      (∫ t in b-h..b, g t) ≤ ∫ t in b-h..b, L :=
        intervalIntegral.integral_mono_on (by linarith)
          (hg.mono_set (by grind [uIcc])) (by simp)
          (by intro t ht; exact (abs_le.mp (hbound t (by constructor <;> linarith [ht.1, ht.2]))).2)
      _ = h*L := by simp
  have hlower : -h*L ≤ ∫ t in a..a+h, g t := by
    calc
      -h*L = ∫ t in a..a+h, -L := by simp
      _ ≤ ∫ t in a..a+h, g t :=
        intervalIntegral.integral_mono_on (by linarith) (by simp)
          (hg.mono_set (by grind [uIcc]))
          (by intro t ht; exact (abs_le.mp (hbound t (by constructor <;> linarith [ht.1, ht.2]))).1)
  linarith

/-- The one-dimensional squared finite-difference error estimate used on convex slices. -/
theorem slice_error_sq_le {g δ : ℝ → ℝ} {a b h L : ℝ}
    (hh : 0 ≤ h) (hhab : h ≤ b-a) (hL : 0 ≤ L)
    (hg : IntervalIntegrable g volume a b)
    (hbound : ∀ t ∈ Icc a b, |g t| ≤ L)
    (hδ : ∀ t ∈ Icc a (b-h), 0 ≤ δ t ∧ δ t ≤ g (t+h)-g t)
    (hδint : IntervalIntegrable (fun t => δ t ^ 2) volume a (b-h)) :
    (∫ t in a..b-h, δ t ^ 2) ≤ 4*L^2*h := by
  have hshift : IntervalIntegrable (fun t => g (t+h)) volume a (b-h) :=
    (hg.comp_add_right h).mono_set (by grind [uIcc])
  have hshort : IntervalIntegrable g volume a (b-h) :=
    hg.mono_set (by grind [uIcc])
  have hpoint : ∀ t ∈ Icc a (b-h), δ t ^ 2 ≤ (2*L)*(g (t+h)-g t) := by
    intro t ht
    have ht0 : t ∈ Icc a b := by constructor <;> linarith [ht.1, ht.2]
    have ht1 : t+h ∈ Icc a b := by constructor <;> linarith [ht.1, ht.2]
    obtain ⟨hgn, hgp⟩ := abs_le.mp (hbound t ht0)
    obtain ⟨hgn', hgp'⟩ := abs_le.mp (hbound (t+h) ht1)
    obtain ⟨hδ0, hδg⟩ := hδ t ht
    have hδL : δ t ≤ 2*L := by linarith
    nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr hδL),
      mul_nonneg (show 0 ≤ 2*L by positivity) (sub_nonneg.mpr hδg)]
  calc
    (∫ t in a..b-h, δ t ^ 2) ≤
        ∫ t in a..b-h, (2*L)*(g (t+h)-g t) :=
      intervalIntegral.integral_mono_on (by linarith) hδint
        ((hshift.sub hshort).const_mul (2*L)) hpoint
    _ = (2*L)*(∫ t in a..b-h, (g (t+h)-g t)) :=
      intervalIntegral.integral_const_mul ..
    _ ≤ (2*L)*(2*L*h) :=
      mul_le_mul_of_nonneg_left (slice_translation_le hh hhab hg hbound) (by positivity)
    _ = 4*L^2*h := by ring

/-- Bounded measurable slice errors have an integrable square. -/
theorem slice_error_sq_integrable {δ : ℝ → ℝ} {a b L : ℝ}
    (hab : a ≤ b) (hL : 0 ≤ L) (hδmeas : Measurable δ)
    (hδ : ∀ t ∈ Icc a b, 0 ≤ δ t ∧ δ t ≤ 2*L) :
    IntervalIntegrable (fun t => δ t ^ 2) volume a b := by
  apply (intervalIntegrable_const :
    IntervalIntegrable (fun _ : ℝ => (2*L)^2) volume a b).mono_fun
  · exact (hδmeas.pow_const 2).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have ht' : t ∈ Icc a b := by
      rw [uIoc_of_le hab] at ht
      exact Ioc_subset_Icc_self ht
    obtain ⟨hδ0, hδL⟩ := hδ t ht'
    simp only [Real.norm_eq_abs, abs_sq]
    nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr hδL)]

/-- Measurable form of the squared finite-difference error estimate. -/
theorem slice_error_sq_le_of_measurable {g δ : ℝ → ℝ} {a b h L : ℝ}
    (hh : 0 ≤ h) (hhab : h ≤ b-a) (hL : 0 ≤ L)
    (hg : IntervalIntegrable g volume a b)
    (hbound : ∀ t ∈ Icc a b, |g t| ≤ L)
    (hδmeas : Measurable δ)
    (hδ : ∀ t ∈ Icc a (b-h), 0 ≤ δ t ∧ δ t ≤ g (t+h)-g t) :
    (∫ t in a..b-h, δ t ^ 2) ≤ 4*L^2*h := by
  apply slice_error_sq_le hh hhab hL hg hbound hδ
  apply slice_error_sq_integrable (by linarith) hL hδmeas
  intro t ht
  refine ⟨(hδ t ht).1, (hδ t ht).2.trans ?_⟩
  have ht0 : t ∈ Icc a b := by constructor <;> linarith [ht.1, ht.2]
  have ht1 : t+h ∈ Icc a b := by constructor <;> linarith [ht.1, ht.2]
  have hg0 := abs_le.mp (hbound t ht0)
  have hg1 := abs_le.mp (hbound (t+h) ht1)
  linarith

/-- Almost-everywhere bounds suffice to establish square integrability on a slice. -/
theorem slice_error_sq_integrable_ae {δ : ℝ → ℝ} {a b L : ℝ}
    (hab : a ≤ b) (hL : 0 ≤ L)
    (hδmeas : AEStronglyMeasurable δ (volume.restrict (Icc a b)))
    (hδ : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ δ t ∧ δ t ≤ 2*L) :
    IntervalIntegrable (fun t => δ t ^ 2) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  apply (integrable_const ((2*L)^2)).mono (hδmeas.pow 2)
  filter_upwards [hδ] with t ht
  simp only [Pi.pow_apply, Real.norm_eq_abs, abs_sq]
  nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]

/-- The quotient error estimate tolerates the null exceptional set of derivative existence. -/
theorem slice_error_sq_le_ae {g δ : ℝ → ℝ} {a b h L : ℝ}
    (hh : 0 ≤ h) (hhab : h ≤ b-a) (hL : 0 ≤ L)
    (hg : IntervalIntegrable g volume a b)
    (hbound : ∀ t ∈ Icc a b, |g t| ≤ L)
    (hδmeas : AEStronglyMeasurable δ (volume.restrict (Icc a (b-h))))
    (hδ : ∀ᵐ t ∂volume.restrict (Icc a (b-h)),
      0 ≤ δ t ∧ δ t ≤ g (t+h)-g t) :
    (∫ t in a..b-h, δ t ^ 2) ≤ 4*L^2*h := by
  have hbδ : ∀ᵐ t ∂volume.restrict (Icc a (b-h)), 0 ≤ δ t ∧ δ t ≤ 2*L := by
    filter_upwards [hδ, ae_restrict_mem measurableSet_Icc] with t ht htm
    refine ⟨ht.1, ht.2.trans ?_⟩
    have hm0 : t ∈ Icc a b := by constructor <;> linarith [htm.1, htm.2]
    have hm1 : t+h ∈ Icc a b := by constructor <;> linarith [htm.1, htm.2]
    have hg0 := abs_le.mp (hbound t hm0)
    have hg1 := abs_le.mp (hbound (t+h) hm1)
    linarith
  have hδint := slice_error_sq_integrable_ae (by linarith) hL hδmeas hbδ
  have hshift : IntervalIntegrable (fun t => g (t+h)) volume a (b-h) :=
    (hg.comp_add_right h).mono_set (by grind [uIcc])
  have hshort : IntervalIntegrable g volume a (b-h) :=
    hg.mono_set (by grind [uIcc])
  have hpoint : ∀ᵐ t ∂volume.restrict (Icc a (b-h)),
      δ t ^ 2 ≤ (2*L)*(g (t+h)-g t) := by
    filter_upwards [hδ, hbδ] with t ht hbt
    nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hbt.2),
      mul_nonneg (show 0 ≤ 2*L by positivity) (sub_nonneg.mpr ht.2)]
  calc
    (∫ t in a..b-h, δ t ^ 2) ≤
        ∫ t in a..b-h, (2*L)*(g (t+h)-g t) :=
      intervalIntegral.integral_mono_ae_restrict (by linarith) hδint
        ((hshift.sub hshort).const_mul (2*L)) hpoint
    _ = (2*L)*(∫ t in a..b-h, (g (t+h)-g t)) :=
      intervalIntegral.integral_const_mul ..
    _ ≤ (2*L)*(2*L*h) :=
      mul_le_mul_of_nonneg_left (slice_translation_le hh hhab hg hbound) (by positivity)
    _ = 4*L^2*h := by ring

end Problem358

end

noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace Problem358

private theorem intervalIntegrable_of_measurable_abs_bound {f : ℝ → ℝ} {M a b : ℝ}
    (hf : Measurable f) (hM : ∀ x, |f x| ≤ M) :
    IntervalIntegrable f volume a b := by
  apply (intervalIntegrable_const :
    IntervalIntegrable (fun _ : ℝ => M) volume a b).mono_fun
  · exact hf.aestronglyMeasurable
  · filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using (hM x).trans (le_abs_self M)

/-- A globally Lipschitz real function has an interval-integrable derivative,
 including at the points where `deriv` is defined to be zero. -/
theorem intervalIntegrable_deriv_of_lipschitz {u : ℝ → ℝ} {L : ℝ≥0}
    (hu : LipschitzWith L u) (a b : ℝ) :
    IntervalIntegrable (deriv u) volume a b := by
  apply intervalIntegrable_of_measurable_abs_bound (measurable_deriv u)
  intro x
  simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := x) hu

/-- Forward quotients of a Lipschitz function have the same bound. -/
theorem abs_forwardQuotient_le_of_lipschitz {u : ℝ → ℝ} {L : ℝ≥0}
    (hu : LipschitzWith L u) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    |forwardQuotient u h x| ≤ L := by
  have hbound : |u (x + h) - u x| ≤ (L : ℝ) * h := by
    simpa [Real.dist_eq, abs_of_pos hh] using hu.dist_le_mul (x + h) x
  rw [forwardQuotient, abs_div, abs_of_pos hh]
  exact (div_le_iff₀ hh).2 hbound

/-- Squared finite-difference errors are integrable without any continuity
 assumption on the derivative. -/
theorem intervalIntegrable_forwardQuotient_error_sq {u : ℝ → ℝ} {L : ℝ≥0}
    (hu : LipschitzWith L u) {h : ℝ} (hh : 0 < h) (a b : ℝ) :
    IntervalIntegrable (fun x => (forwardQuotient u h x - deriv u x) ^ 2) volume a b := by
  have hq : Measurable (forwardQuotient u h) := by
    unfold forwardQuotient
    exact ((hu.continuous.measurable.comp (measurable_id.add_const h)).sub
      hu.continuous.measurable).div_const h
  apply intervalIntegrable_of_measurable_abs_bound
    (M := (2 * (L : ℝ)) ^ 2) ((hq.sub (measurable_deriv u)).pow_const 2)
  intro x
  change |(forwardQuotient u h x - deriv u x) ^ 2| ≤ (2 * (L : ℝ)) ^ 2
  have hd : |deriv u x| ≤ (L : ℝ) := by
    simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := x) hu
  have hq' := abs_forwardQuotient_le_of_lipschitz hu hh x
  have he : |forwardQuotient u h x - deriv u x| ≤ 2 * (L : ℝ) := by
    exact (abs_sub _ _).trans (by linarith)
  have he0 := abs_nonneg (forwardQuotient u h x - deriv u x)
  have hL : 0 ≤ (L : ℝ) := L.coe_nonneg
  rw [abs_sq]
  nlinarith [sq_abs (forwardQuotient u h x - deriv u x)]

/-- Convex quotient control holds almost everywhere for globally convex
 Lipschitz functions, because translation preserves null sets. -/
theorem ae_convex_forwardQuotient_error_sq_le {u : ℝ → ℝ} {L : ℝ≥0}
    (hu : ConvexOn ℝ univ u) (hLip : LipschitzWith L u) {h : ℝ} (hh : 0 < h) :
    ∀ᵐ x : ℝ, (forwardQuotient u h x - deriv u x) ^ 2 ≤
      2 * (L : ℝ) * (deriv u (x + h) - deriv u x) := by
  have hd : ∀ᵐ x : ℝ, DifferentiableAt ℝ u x := hLip.ae_differentiableAt
  have hshift : ∀ᵐ x : ℝ, DifferentiableAt ℝ u (x + h) :=
    (measurePreserving_add_right volume h).quasiMeasurePreserving.ae hd
  filter_upwards [hd, hshift] with x hx hxh
  apply convex_forwardQuotient_error_sq_le hu (mem_univ x) (mem_univ (x+h)) hh
    hx.hasDerivAt hxh.hasDerivAt
  · simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := x) hLip
  · simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := x+h) hLip

/-- The squared quotient error integrated on the allowed part of a slice is
 bounded by `4 L² h`, with no everywhere-differentiability assumption. -/
theorem convex_slice_quotient_error_sq_le {u : ℝ → ℝ} {L : ℝ≥0}
    (hu : ConvexOn ℝ univ u) (hLip : LipschitzWith L u)
    {a b h : ℝ} (hh : 0 < h) (hhab : h ≤ b - a) :
    (∫ x in a..b-h, (forwardQuotient u h x - deriv u x) ^ 2) ≤
      4 * (L : ℝ) ^ 2 * h := by
  have hint := intervalIntegrable_deriv_of_lipschitz hLip a b
  have hshift : IntervalIntegrable (fun x => deriv u (x+h)) volume a (b-h) :=
    (hint.comp_add_right h).mono_set (by grind [uIcc])
  have hshort : IntervalIntegrable (deriv u) volume a (b-h) :=
    hint.mono_set (by grind [uIcc])
  have hb : ∀ x ∈ Icc a b, |deriv u x| ≤ (L : ℝ) := by
    intro x _
    simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := x) hLip
  calc
    (∫ x in a..b-h, (forwardQuotient u h x - deriv u x) ^ 2) ≤
        ∫ x in a..b-h, 2 * (L : ℝ) * (deriv u (x+h) - deriv u x) :=
      intervalIntegral.integral_mono_ae (by linarith)
        (intervalIntegrable_forwardQuotient_error_sq hLip hh a (b-h))
        ((hshift.sub hshort).const_mul _) (ae_convex_forwardQuotient_error_sq_le hu hLip hh)
    _ = (2 * (L : ℝ)) * (∫ x in a..b-h, deriv u (x+h) - deriv u x) :=
      intervalIntegral.integral_const_mul ..
    _ ≤ (2 * (L : ℝ)) * (2 * (L : ℝ) * h) :=
      mul_le_mul_of_nonneg_left
        (slice_translation_le hh.le hhab hint hb) (by positivity)
    _ = 4 * (L : ℝ) ^ 2 * h := by ring

/-- The difference of derivatives of two Lipschitz real functions is bounded
 pointwise, including the default values at nondifferentiability points. -/
theorem sq_deriv_sub_le_of_lipschitz {u v : ℝ → ℝ} {L₀ L₁ : ℝ≥0}
    (hu : LipschitzWith L₀ u) (hv : LipschitzWith L₁ v) (x : ℝ) :
    (deriv u x - deriv v x) ^ 2 ≤ ((L₀ : ℝ) + (L₁ : ℝ)) ^ 2 := by
  have hdu : |deriv u x| ≤ (L₀ : ℝ) := by
    simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := x) hu
  have hdv : |deriv v x| ≤ (L₁ : ℝ) := by
    simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := x) hv
  have hd : |deriv u x - deriv v x| ≤ (L₀ : ℝ) + (L₁ : ℝ) :=
    (abs_sub _ _).trans (add_le_add hdu hdv)
  have hd0 := abs_nonneg (deriv u x - deriv v x)
  nlinarith [sq_abs (deriv u x - deriv v x)]

/-- Squared derivative differences are interval-integrable. -/
theorem intervalIntegrable_sq_deriv_sub_of_lipschitz {u v : ℝ → ℝ} {L₀ L₁ : ℝ≥0}
    (hu : LipschitzWith L₀ u) (hv : LipschitzWith L₁ v) (a b : ℝ) :
    IntervalIntegrable (fun x => (deriv u x - deriv v x) ^ 2) volume a b := by
  apply intervalIntegrable_of_measurable_abs_bound
    (M := ((L₀ : ℝ) + (L₁ : ℝ)) ^ 2)
    (((measurable_deriv u).sub (measurable_deriv v)).pow_const 2)
  intro x
  change |(deriv u x - deriv v x) ^ 2| ≤ ((L₀ : ℝ) + (L₁ : ℝ)) ^ 2
  rw [abs_sq]
  exact sq_deriv_sub_le_of_lipschitz hu hv x

/-- Boundary-strip estimate for squared derivative differences. -/
theorem integral_sq_deriv_sub_le_of_lipschitz {u v : ℝ → ℝ} {L₀ L₁ : ℝ≥0}
    (hu : LipschitzWith L₀ u) (hv : LipschitzWith L₁ v) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, (deriv u x - deriv v x) ^ 2) ≤
      ((L₀ : ℝ) + (L₁ : ℝ)) ^ 2 * (b - a) := by
  calc
    (∫ x in a..b, (deriv u x - deriv v x) ^ 2) ≤
        ∫ _x in a..b, ((L₀ : ℝ) + (L₁ : ℝ)) ^ 2 :=
      intervalIntegral.integral_mono_on hab
        (intervalIntegrable_sq_deriv_sub_of_lipschitz hu hv a b)
        intervalIntegrable_const (fun x _ => sq_deriv_sub_le_of_lipschitz hu hv x)
    _ = _ := by simp [mul_comm]

end Problem358

end

end OAI
