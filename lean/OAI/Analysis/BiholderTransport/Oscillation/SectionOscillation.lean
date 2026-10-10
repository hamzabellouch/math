import Mathlib
import OAI.Analysis.BiholderTransport.Volume.RadialNull
import OAI.Analysis.BiholderTransport.Duality.CompactDual

namespace OAI

section
section
noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

section SectionOscillation
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

def sectionOscillation (u v : M → ℝ) (x : M) (r : ℝ) : ℝ :=
  sSup (v '' gapSection u v x r) - sInf (v '' gapSection u v x r)

omit [Nonempty M] in
lemma isCompact_gapSection {u v : M → ℝ} (hv : Continuous v) (x : M) (r : ℝ) :
    IsCompact (gapSection u v x r) := by
  apply IsClosed.isCompact
  exact isClosed_le ((continuous_const.add (continuous_cost_right x)).add hv) continuous_const

lemma gapSection_nonempty {u v : M → ℝ} (hv : Continuous v)
    (huv : IsCostDualPair u v) (x : M) {r : ℝ} (hr : 0 ≤ r) :
    (gapSection u v x r).Nonempty := by
  obtain ⟨y, hy⟩ := dualPair_contact_left hv huv x
  exact ⟨y, by simpa only [gapSection, mem_ofPred_eq, hy] using hr⟩

lemma sectionOscillation_extrema {u v : M → ℝ} (hv : Continuous v)
    (huv : IsCostDualPair u v) (x : M) {r : ℝ} (hr : 0 ≤ r) :
    ∃ y0 ∈ gapSection u v x r, ∃ y1 ∈ gapSection u v x r,
      (∀ y ∈ gapSection u v x r, v y0 ≤ v y) ∧
      (∀ y ∈ gapSection u v x r, v y ≤ v y1) ∧
      sectionOscillation u v x r = v y1 - v y0 := by
  have hc := isCompact_gapSection (u := u) hv x r
  have hn := gapSection_nonempty hv huv x hr
  obtain ⟨y0, hy0, hmin⟩ := hc.exists_isMinOn hn hv.continuousOn
  obtain ⟨y1, hy1, hmax⟩ := hc.exists_isMaxOn hn hv.continuousOn
  have hleast : IsLeast (v '' gapSection u v x r) (v y0) := by
    refine ⟨mem_image_of_mem v hy0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmin hy
  have hgreatest : IsGreatest (v '' gapSection u v x r) (v y1) := by
    refine ⟨mem_image_of_mem v hy1, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmax hy
  exact ⟨y0, hy0, y1, hy1, fun _ hy => hmin hy, fun _ hy => hmax hy,
    by rw [sectionOscillation, hleast.csInf_eq, hgreatest.csSup_eq]⟩

lemma sectionOscillation_nonneg {u v : M → ℝ} (hv : Continuous v)
    (huv : IsCostDualPair u v) (x : M) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ sectionOscillation u v x r := by
  obtain ⟨y0, _, y1, hy1, hmin, _, heq⟩ := sectionOscillation_extrema hv huv x hr
  rw [heq]
  exact sub_nonneg.mpr (hmin y1 hy1)

lemma sectionOscillation_mono {u v : M → ℝ} (hv : Continuous v)
    (huv : IsCostDualPair u v) (x : M) {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    sectionOscillation u v x r ≤ sectionOscillation u v x R := by
  obtain ⟨y0, hy0, y1, hy1, _, _, heq⟩ := sectionOscillation_extrema hv huv x hr
  obtain ⟨z0, _, z1, _, hmin, hmax, heq'⟩ :=
    sectionOscillation_extrema hv huv x (hr.trans hrR)
  have h0 := hmin y0 (hy0.trans hrR)
  have h1 := hmax y1 (hy1.trans hrR)
  rw [heq, heq']
  linarith

lemma sectionOscillation_le_diam_sq {u v : M → ℝ} (hu : Continuous u)
    (hv : Continuous v) (huv : IsCostDualPair u v) (x : M) {r : ℝ} (hr : 0 ≤ r) :
    sectionOscillation u v x r ≤ Metric.diam (univ : Set M) ^ 2 := by
  let D : ℝ≥0 := ⟨Metric.diam (univ : Set M), Metric.diam_nonneg⟩
  have hD (x y : M) : dist x y ≤ D :=
    Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)
  have hLip : LipschitzWith D v := by
    rw [huv.2]
    exact cTransform_lipschitz hu hD
  obtain ⟨y0, _, y1, _, _, _, heq⟩ := sectionOscillation_extrema hv huv x hr
  have hh := hLip.dist_le_mul y1 y0
  rw [Real.dist_eq] at hh
  rw [heq]
  calc
    v y1 - v y0 ≤ |v y1 - v y0| := le_abs_self _
    _ ≤ (D : ℝ) * dist y1 y0 := hh
    _ ≤ (D : ℝ) ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left (hD y1 y0) D.coe_nonneg]

variable [MeasurableSpace M] [BorelSpace M]

def densityDualClass (vol : Measure M) (lam cap : ℝ) (x0 : M) :
    Set ((M →ᵇ ℝ) × (M →ᵇ ℝ)) :=
  {uv | uv ∈ normalizedDualPairs x0 ∧
    ∃ rho0 rho1 : M → ℝ, AdmissibleDensity vol lam cap rho0 ∧
      AdmissibleDensity vol lam cap rho1 ∧
      ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
        dualObjective (densityMeasure vol rho0) (densityMeasure vol rho1) uv ≤
          dualObjective (densityMeasure vol rho0) (densityMeasure vol rho1) (a,b)}

lemma densityDualClass_nonempty {vol : Measure M} {lam cap : ℝ} (hlam : 0 < lam)
    (hclass : ∃ rho : M → ℝ, AdmissibleDensity vol lam cap rho) (x0 : M) :
    (densityDualClass vol lam cap x0).Nonempty := by
  obtain ⟨rho, hrho⟩ := hclass
  have := densityMeasure_probability hlam hrho
  let mu := densityMeasure vol rho
  obtain ⟨uv, huv, hmin⟩ := exists_minimizing_normalizedDualPair mu mu x0
  refine ⟨uv, huv, rho, rho, hrho, hrho, ?_⟩
  intro a b hab
  exact (hmin (normalizeDualPair_mem x0 b)).trans
    (dualObjective_normalize_le mu mu x0 a b hab)

omit [BorelSpace M] in
lemma densityDualClass_isDual {vol : Measure M} {lam cap : ℝ} {x0 : M}
    {uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)} (h : uv ∈ densityDualClass vol lam cap x0) :
    IsCostDualPair uv.1 uv.2 := by
  constructor
  · exact congrArg (fun f : M →ᵇ ℝ => (f : M → ℝ)) h.1.2.1.symm
  · exact congrArg (fun f : M →ᵇ ℝ => (f : M → ℝ)) h.1.2.2.symm

def classSectionOscillations (vol : Measure M) (lam cap : ℝ) (x0 : M) (r : ℝ) : Set ℝ :=
  {a | ∃ uv ∈ densityDualClass vol lam cap x0, ∃ x : M,
    a = sectionOscillation uv.1 uv.2 x r}

def classOscillation (vol : Measure M) (lam cap : ℝ) (x0 : M) (r : ℝ) : ℝ :=
  sSup (classSectionOscillations vol lam cap x0 r)

omit [BorelSpace M] in
lemma classSectionOscillations_nonempty {vol : Measure M} {lam cap : ℝ} {x0 : M}
    (hc : (densityDualClass vol lam cap x0).Nonempty) (r : ℝ) :
    (classSectionOscillations vol lam cap x0 r).Nonempty := by
  obtain ⟨uv, huv⟩ := hc
  exact ⟨_, uv, huv, x0, rfl⟩

omit [BorelSpace M] in
lemma classSectionOscillations_bddAbove {vol : Measure M} {lam cap : ℝ} {x0 : M}
    {r : ℝ} (hr : 0 ≤ r) : BddAbove (classSectionOscillations vol lam cap x0 r) := by
  refine ⟨Metric.diam (univ : Set M) ^ 2, ?_⟩
  rintro _ ⟨uv, huv, x, rfl⟩
  exact sectionOscillation_le_diam_sq uv.1.continuous uv.2.continuous
    (densityDualClass_isDual huv) x hr

omit [BorelSpace M] in
lemma sectionOscillation_le_classOscillation {vol : Measure M} {lam cap : ℝ} {x0 : M}
    {uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)} (huv : uv ∈ densityDualClass vol lam cap x0)
    (x : M) {r : ℝ} (hr : 0 ≤ r) :
    sectionOscillation uv.1 uv.2 x r ≤ classOscillation vol lam cap x0 r := by
  exact le_csSup (classSectionOscillations_bddAbove hr) ⟨uv, huv, x, rfl⟩

omit [BorelSpace M] in
lemma classOscillation_bounds {vol : Measure M} {lam cap : ℝ} {x0 : M}
    (hc : (densityDualClass vol lam cap x0).Nonempty) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ classOscillation vol lam cap x0 r ∧
      classOscillation vol lam cap x0 r ≤ Metric.diam (univ : Set M) ^ 2 := by
  constructor
  · obtain ⟨uv, huv⟩ := hc
    exact (sectionOscillation_nonneg uv.2.continuous (densityDualClass_isDual huv) x0 hr).trans
      (sectionOscillation_le_classOscillation huv x0 hr)
  · apply csSup_le (classSectionOscillations_nonempty hc r)
    rintro _ ⟨uv, huv, x, rfl⟩
    exact sectionOscillation_le_diam_sq uv.1.continuous uv.2.continuous
      (densityDualClass_isDual huv) x hr

omit [BorelSpace M] in
lemma classOscillation_monotone {vol : Measure M} {lam cap : ℝ} {x0 : M}
    (hc : (densityDualClass vol lam cap x0).Nonempty) :
    MonotoneOn (classOscillation vol lam cap x0) (Ici 0) := by
  intro r hr R hR hrR
  apply csSup_le (classSectionOscillations_nonempty hc r)
  rintro _ ⟨uv, huv, x, rfl⟩
  exact (sectionOscillation_mono uv.2.continuous (densityDualClass_isDual huv) x hr hrR).trans
    (sectionOscillation_le_classOscillation huv x hR)

omit [BorelSpace M] in

lemma exists_section_with_large_oscillation {vol : Measure M} {lam cap : ℝ} {x0 : M}
    (hc : (densityDualClass vol lam cap x0).Nonempty) {r q : ℝ}
    (hr : 0 ≤ r) (hq : q < classOscillation vol lam cap x0 r) :
    ∃ uv ∈ densityDualClass vol lam cap x0, ∃ x y0 y1 : M,
      y0 ∈ gapSection uv.1 uv.2 x r ∧ y1 ∈ gapSection uv.1 uv.2 x r ∧
      (∀ y ∈ gapSection uv.1 uv.2 x r, uv.2 y0 ≤ uv.2 y) ∧
      (∀ y ∈ gapSection uv.1 uv.2 x r, uv.2 y ≤ uv.2 y1) ∧
      sectionOscillation uv.1 uv.2 x r = uv.2 y1 - uv.2 y0 ∧
      q < uv.2 y1 - uv.2 y0 := by
  obtain ⟨a, ⟨uv, huv, x, rfl⟩, ha⟩ := exists_lt_of_lt_csSup
    (classSectionOscillations_nonempty hc r) hq
  obtain ⟨y0, hy0, y1, hy1, hmin, hmax, heq⟩ :=
    sectionOscillation_extrema uv.2.continuous (densityDualClass_isDual huv) x hr
  exact ⟨uv, huv, x, y0, y1, hy0, hy1, hmin, hmax, heq, heq ▸ ha⟩

def reverseNormalizedPair (x0 : M) (uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)) :
    (M →ᵇ ℝ) × (M →ᵇ ℝ) :=
  (uv.2 + BoundedContinuousFunction.const M (-uv.2 x0),
    uv.1 + BoundedContinuousFunction.const M (uv.2 x0))

omit [MeasurableSpace M] [BorelSpace M] in
lemma reverseNormalizedPair_mem {x0 : M} {uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)}
    (huv : uv ∈ normalizedDualPairs x0) :
    reverseNormalizedPair x0 uv ∈ normalizedDualPairs x0 := by
  change (uv.2 x0 + -uv.2 x0 = 0) ∧ _ ∧ _
  refine ⟨add_neg_cancel _, ?_, ?_⟩
  · apply BoundedContinuousFunction.ext
    intro x
    change cTransform (fun y => uv.1 y + uv.2 x0) x = uv.2 x + -uv.2 x0
    rw [cTransform_add_const uv.1.continuous]
    have hh := congrArg (fun f : M →ᵇ ℝ => f x) huv.2.2
    change cTransform uv.1 x = uv.2 x at hh
    change cTransform uv.1 x - uv.2 x0 = uv.2 x + -uv.2 x0
    rw [hh]
    ring
  · apply BoundedContinuousFunction.ext
    intro x
    change cTransform (fun y => uv.2 y + -uv.2 x0) x = uv.1 x + uv.2 x0
    rw [cTransform_add_const uv.2.continuous]
    have hh := congrArg (fun f : M →ᵇ ℝ => f x) huv.2.1
    change cTransform uv.2 x = uv.1 x at hh
    change cTransform uv.2 x - -uv.2 x0 = uv.1 x + uv.2 x0
    rw [hh]
    ring

lemma densityDualClass_reverse {vol : Measure M} {lam cap : ℝ} (hlam : 0 < lam)
    {x0 : M} {uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)}
    (huv : uv ∈ densityDualClass vol lam cap x0) :
    reverseNormalizedPair x0 uv ∈ densityDualClass vol lam cap x0 := by
  obtain ⟨hnorm, rho0, rho1, hrho0, hrho1, hmin⟩ := huv
  let := densityMeasure_probability hlam hrho0
  let := densityMeasure_probability hlam hrho1
  refine ⟨reverseNormalizedPair_mem hnorm, rho1, rho0, hrho1, hrho0, ?_⟩
  intro a b hab
  have hba : ∀ x y, 0 ≤ contactGap b a x y := by
    intro x y
    have hh := hab y x
    dsimp [contactGap] at hh ⊢
    rw [cost_symm y x] at hh
    linarith
  have hh := hmin b a hba
  rw [reverseNormalizedPair, dualObjective_add_constants]
  dsimp [dualObjective] at hh ⊢
  linarith

omit [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma reverseNormalizedPair_gap (x0 : M) (uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)) (x y : M) :
    contactGap (reverseNormalizedPair x0 uv).1 (reverseNormalizedPair x0 uv).2 x y =
      contactGap uv.1 uv.2 y x := by
  change (uv.2 x + -uv.2 x0) + cost x y + (uv.1 y + uv.2 x0) = _
  rw [contactGap, cost_symm y x]
  ring

end SectionOscillation

open Filter

lemma exists_small_step (f : ℝ → ℝ) (a h q : ℝ) {m : ℕ} (hm : 0 < m)
    (hbound : f (a + m * h) - f a ≤ m * q) :
    ∃ i : ℕ, i < m ∧ f (a + (i + 1) * h) - f (a + i * h) ≤ q := by
  have hsum : (∑ i ∈ Finset.range m, (f (a + (i + 1) * h) - f (a + i * h))) ≤
      ∑ _i ∈ Finset.range m, q := by
    have ht := Finset.sum_range_sub (fun i : ℕ => f (a + i * h)) m
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero] at ht
    rw [ht]
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hbound
  obtain ⟨i, hi, hb⟩ := Finset.exists_le_of_sum_le ⟨0, Finset.mem_range.mpr hm⟩ hsum
  exact ⟨i, Finset.mem_range.mp hi, hb⟩

lemma logarithmic_plateau_quantitative {f : ℝ → ℝ} (hmono : Monotone f)
    (hzero : ∀ s, 0 ≤ f s)
    (hsub : ∀ eps : ℝ, 0 < eps → ∀ L : ℝ, ∃ N : ℝ, L ≤ N ∧ f N ≤ eps * N)
    {J : ℝ} (hJ : 1 ≤ J) :
    ∃ A B : ℝ, J ^ 2 ≤ A ∧ B = A + J ∧
      f B - f A ≤ J⁻¹ ∧ f B ≤ A / J ^ 2 := by
  have hJ0 : 0 < J := lt_of_lt_of_le zero_lt_one hJ
  have hden : 0 < 4 * J ^ 2 := by positivity
  obtain ⟨N, hN, hfN⟩ := hsub (4 * J ^ 2)⁻¹ (inv_pos.mpr hden) (4 * J ^ 2)
  have hN0 : 0 ≤ N := (le_of_lt hden).trans hN
  let m : ℕ := ⌊N / (2 * J)⌋₊
  have hmle : (m : ℝ) ≤ N / (2 * J) := Nat.floor_le (by positivity)
  have hmlt : N / (2 * J) < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmle' : 2 * J * m ≤ N := by
    have hh := (le_div_iff₀ (show 0 < 2 * J by positivity)).mp hmle
    nlinarith
  have hmlt' : N < 2 * J * (m + 1) := by
    have hh := (div_lt_iff₀ (show 0 < 2 * J by positivity)).mp hmlt
    nlinarith
  have hmJ : J ≤ (m : ℝ) := by nlinarith
  have hm1 : (1 : ℝ) ≤ m := hJ.trans hmJ
  have hmpos : 0 < m := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm1)
  have hNupper : N ≤ 4 * J * m := by nlinarith
  have hfNm : f N ≤ (m : ℝ) / J := by
    have hh : f N * (4 * J ^ 2) ≤ N := by
      calc
        f N * (4 * J ^ 2) ≤ ((4 * J ^ 2)⁻¹ * N) * (4 * J ^ 2) :=
          mul_le_mul_of_nonneg_right hfN hden.le
        _ = N := by field_simp
    apply (le_div_iff₀ hJ0).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hNupper) (show 0 ≤ J by positivity)]
  have hsum : f (J * m + (m : ℝ) * J) - f (J * m) ≤ (m : ℝ) * J⁻¹ := by
    have htop := hmono (show J * m + (m : ℝ) * J ≤ N by nlinarith)
    have hbot := hzero (J * m)
    rw [div_eq_mul_inv] at hfNm
    linarith
  obtain ⟨i, hi, hstep⟩ := exists_small_step f (J * m) J J⁻¹ hmpos hsum
  let A := J * m + (i : ℝ) * J
  let B := J * m + ((i : ℝ) + 1) * J
  have hA : J ^ 2 ≤ A := by
    dsimp [A]
    nlinarith [Nat.cast_nonneg (α := ℝ) i]
  have hB : B ≤ N := by
    have hi' : (i : ℝ) + 1 ≤ m := by exact_mod_cast hi
    dsimp [B]
    nlinarith
  refine ⟨A, B, hA, by dsimp [A, B]; ring, hstep, ?_⟩
  calc
    f B ≤ f N := hmono hB
    _ ≤ (m : ℝ) / J := hfNm
    _ ≤ A / J ^ 2 := by
      apply (div_le_div_iff₀ hJ0 (sq_pos_of_pos hJ0)).mpr
      dsimp [A]
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) i) (sq_nonneg J)]

def HasPowerUpperBound (F : ℝ → ℝ) : Prop :=
  ∃ beta C r0 : ℝ, 0 < beta ∧ 0 < C ∧ 0 < r0 ∧
    ∀ r : ℝ, 0 < r → r < r0 → F r ≤ C * r ^ beta

lemma log_sublinear_of_no_power {F : ℝ → ℝ} {CF : ℝ} (hCF : 0 < CF)
    (hFpos : ∀ r : ℝ, 0 < r → 0 < F r) (hno : ¬ HasPowerUpperBound F) :
    ∀ eps : ℝ, 0 < eps → ∀ L : ℝ, ∃ N : ℝ, L ≤ N ∧
      Real.log (CF / F (Real.exp (-N))) ≤ eps * N := by
  intro eps heps L
  have hbad : ∃ r : ℝ, 0 < r ∧ r < Real.exp (-L) ∧ CF * r ^ eps < F r := by
    by_contra! hgood
    exact hno ⟨eps, CF, Real.exp (-L), heps, hCF, Real.exp_pos _,
      fun r hr hr0 => hgood r hr hr0⟩
  obtain ⟨r, hr, hr0, hbad⟩ := hbad
  refine ⟨-Real.log r, ?_, ?_⟩
  · have hh := Real.log_lt_log hr hr0
    rw [Real.log_exp] at hh
    linarith
  · have hh := Real.log_lt_log (mul_pos hCF (Real.rpow_pos_of_pos hr eps)) hbad
    rw [Real.log_mul hCF.ne' (Real.rpow_pos_of_pos hr eps).ne', Real.log_rpow hr] at hh
    rw [neg_neg, Real.exp_log hr, Real.log_div hCF.ne' (hFpos r hr).ne']
    linarith

lemma logarithmic_profile_nonneg {F : ℝ → ℝ} {CF : ℝ}
    (hFpos : ∀ r : ℝ, 0 < r → 0 < F r)
    (hbound : ∀ r : ℝ, 0 < r → F r ≤ CF) (s : ℝ) :
    0 ≤ Real.log (CF / F (Real.exp (-s))) := by
  apply Real.log_nonneg
  exact (one_le_div (hFpos _ (Real.exp_pos _))).mpr (hbound _ (Real.exp_pos _))

lemma logarithmic_profile_monotone {F : ℝ → ℝ} {CF : ℝ} (hCF : 0 < CF)
    (hFpos : ∀ r : ℝ, 0 < r → 0 < F r) (hmono : MonotoneOn F (Ioi 0)) :
    Monotone (fun s : ℝ => Real.log (CF / F (Real.exp (-s)))) := by
  intro a b hab
  apply Real.log_le_log (div_pos hCF (hFpos _ (Real.exp_pos _)))
  exact div_le_div_of_nonneg_left hCF.le (hFpos _ (Real.exp_pos _))
    (hmono (Real.exp_pos _) (Real.exp_pos _) (Real.exp_le_exp.mpr (neg_le_neg hab)))

lemma no_power_logarithmic_plateau {F : ℝ → ℝ} {CF : ℝ} (hCF : 0 < CF)
    (hFpos : ∀ r : ℝ, 0 < r → 0 < F r)
    (hbound : ∀ r : ℝ, 0 < r → F r ≤ CF) (hmono : MonotoneOn F (Ioi 0))
    (hno : ¬ HasPowerUpperBound F) {J : ℝ} (hJ : 1 ≤ J) :
    ∃ A B : ℝ, J ^ 2 ≤ A ∧ B = A + J ∧
      Real.log (CF / F (Real.exp (-B))) - Real.log (CF / F (Real.exp (-A))) ≤ J⁻¹ ∧
      Real.log (CF / F (Real.exp (-B))) ≤ A / J ^ 2 := by
  exact logarithmic_plateau_quantitative
    (logarithmic_profile_monotone hCF hFpos hmono)
    (logarithmic_profile_nonneg hFpos hbound)
    (log_sublinear_of_no_power hCF hFpos hno) hJ

lemma positive_of_no_power {F : ℝ → ℝ} (hmono : MonotoneOn F (Ioi 0))
    (hno : ¬ HasPowerUpperBound F) {r : ℝ} (hr : 0 < r) : 0 < F r := by
  by_contra! hF
  apply hno
  refine ⟨1, 1, r, by norm_num, by norm_num, hr, ?_⟩
  intro t ht htr
  have hh := hmono ht hr htr.le
  simpa only [Real.rpow_one, one_mul] using hh.trans (hF.trans ht.le)

lemma no_power_gap_scale_plateau {F : ℝ → ℝ} {CF : ℝ} (hCF : 0 < CF)
    (hbound : ∀ r : ℝ, 0 < r → F r ≤ CF) (hmono : MonotoneOn F (Ioi 0))
    (hno : ¬ HasPowerUpperBound F) {J : ℝ} (hJ : 1 ≤ J) :
    ∃ A : ℝ, J ^ 2 ≤ A ∧
      F (Real.exp (-A)) ≤ Real.exp J⁻¹ * F (Real.exp (-(A + J))) ∧
      |Real.log (F (Real.exp (-(A + J))))| ≤ |Real.log CF| + A / J ^ 2 := by
  have hpos : ∀ r : ℝ, 0 < r → 0 < F r := fun _ hr => positive_of_no_power hmono hno hr
  obtain ⟨A, B, hA, rfl, hinc, hval⟩ :=
    no_power_logarithmic_plateau hCF hpos hbound hmono hno hJ
  have hpA := hpos (Real.exp (-A)) (Real.exp_pos _)
  have hpB := hpos (Real.exp (-(A+J))) (Real.exp_pos _)
  have hfnonneg := logarithmic_profile_nonneg hpos hbound (A + J)
  rw [Real.log_div hCF.ne' hpB.ne', Real.log_div hCF.ne' hpA.ne'] at hinc
  rw [Real.log_div hCF.ne' hpB.ne'] at hval hfnonneg
  refine ⟨A, hA, ?_, ?_⟩
  · have hlog : Real.log (F (Real.exp (-A))) ≤ J⁻¹ + Real.log (F (Real.exp (-(A+J)))) := by
      linarith
    have hh := Real.exp_le_exp.mpr hlog
    simpa only [Real.exp_add, Real.exp_log hpA, Real.exp_log hpB] using hh
  · calc
      |Real.log (F (Real.exp (-(A+J))))| =
          |Real.log CF - (Real.log CF - Real.log (F (Real.exp (-(A+J)))))| := by ring_nf
      _ ≤ |Real.log CF| + |Real.log CF - Real.log (F (Real.exp (-(A+J))))| := abs_sub _ _
      _ ≤ |Real.log CF| + A / J ^ 2 := by rw [abs_of_nonneg hfnonneg]; linarith

end WeakMTWTransport
end
end
end

end OAI
