import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MovingParameters
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MeanC

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff
open Finset Classical
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations

def prefixAverage (f : ℕ → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, f n

def absPrimeDefect (f : ℕ → ℂ) (p : ℕ) : ℝ :=
  if p.Prime then (1 - ‖f p‖) / (p : ℝ) else 0

def absDefect (f : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, (1 - ‖f p‖) / (p : ℝ)

def magnitude (f : ℕ → ℂ) (n : ℕ) : ℂ := (‖f n‖ : ℝ)

@[simp] lemma norm_magnitude (f : ℕ → ℂ) (n : ℕ) :
    ‖magnitude f n‖ = ‖f n‖ := by
  simp [magnitude]

lemma magnitude_oneBounded {f : ℕ → ℂ} (hf : OneBounded f) :
    OneBounded (magnitude f) := by
  intro n
  simpa using hf n

lemma magnitude_multiplicative {f : ℕ → ℂ} (hf : Multiplicative f) :
    Multiplicative (magnitude f) := by
  intro m n hm hn hmn
  simp only [magnitude, hf m n hm hn hmn, norm_mul, Complex.ofReal_mul]

lemma absPrimeDefect_nonneg {f : ℕ → ℂ} (hf : OneBounded f) (p : ℕ) :
    0 ≤ absPrimeDefect f p := by
  unfold absPrimeDefect
  split_ifs
  · exact div_nonneg (sub_nonneg.mpr (hf p)) (Nat.cast_nonneg p)
  · exact le_rfl

lemma absDefect_eq_sum (f : ℕ → ℂ) (N : ℕ) :
    absDefect f N = ∑ p ∈ Finset.range (N + 1), absPrimeDefect f p := by
  have he : (Finset.Icc 2 N).filter Nat.Prime =
      (Finset.range (N + 1)).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hpN⟩, hp⟩
      exact ⟨by omega, hp⟩
    · rintro ⟨hpN, hp⟩
      exact ⟨⟨hp.two_le, by omega⟩, hp⟩
  simp only [absDefect, he, Finset.sum_filter, absPrimeDefect]

lemma absDefect_tendsto {f : ℕ → ℂ} (hf : OneBounded f)
    (hd : ¬ Summable (absPrimeDefect f)) :
    Tendsto (absDefect f) atTop atTop := by
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (absPrimeDefect_nonneg hf)).mp hd
  have hs : Tendsto (fun N : ℕ => N + 1) atTop atTop := by
    exact tendsto_atTop_mono (fun n => Nat.le_add_right n 1) tendsto_id
  simpa only [Function.comp_def, ← absDefect_eq_sum] using ht.comp hs

lemma absDefect_le_distanceSq (f : ℕ → ℂ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) (N : ℕ) :
    absDefect f N ≤ distanceSq (magnitude f) χ t N := by
  unfold absDefect distanceSq
  rw [Nat.floor_natCast]
  apply Finset.sum_le_sum
  intro p hp
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
  apply sub_le_sub_left
  have ht : ‖χ (p : ZMod q) *
      Complex.exp ((t * Real.log (p : ℝ) : ℝ) * Complex.I)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_exp]
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, zero_mul, sub_self, Real.exp_zero, mul_one]
      using χ.norm_le_one (p : ZMod q)
  apply (Complex.re_le_norm _).trans
  rw [norm_mul, norm_star, norm_magnitude]
  exact mul_le_of_le_one_right (norm_nonneg _) ht

theorem magnitude_uniformlyNonpretentious {f : ℕ → ℂ} (hf : OneBounded f)
    (hd : ¬ Summable (absPrimeDefect f)) :
    UniformlyNonpretentious (magnitude f) := by
  intro q hq χ
  apply tendsto_atTop.mpr
  intro M
  filter_upwards [(absDefect_tendsto hf hd).eventually_ge_atTop ((max M 0)^2)]
    with N hN
  apply le_csInf
  · exact ⟨distance (magnitude f) χ 0 N, 0,
      ⟨neg_nonpos.mpr (Nat.cast_nonneg N), Nat.cast_nonneg N⟩, rfl⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact (le_max_left M 0).trans (Real.le_sqrt_of_sq_le
      (hN.trans (absDefect_le_distanceSq f χ t N)))

theorem prefixAverage_tendsto_zero {f : ℕ → ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f) :
    Tendsto (prefixAverage f) atTop (nhds 0) := by
  let parameters : ℕ → PretentiousEuler.MovingParameters :=
    fun N => ⟨(N, 0), by simp; positivity⟩
  have hp : Tendsto parameters atTop PretentiousEuler.movingFilter := by
    apply tendsto_comap_iff.mpr
    exact tendsto_id
  have ht := (PretentiousEuler.moving_multiplicative_mean_tendsto_zero hf hm hNP).comp hp
  change Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
    OrdinaryArchimedeanTwist.twist f 0 n) atTop (nhds 0) at ht
  change Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, f n) atTop (nhds 0)
  simpa only [OrdinaryArchimedeanTwist.twist, zero_mul, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, mul_one] using ht

theorem magnitude_mean_zero {f : ℕ → ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hd : ¬ Summable (absPrimeDefect f)) :
    Tendsto (prefixAverage (magnitude f)) atTop (nhds 0) :=
  prefixAverage_tendsto_zero (magnitude_oneBounded hf) (magnitude_multiplicative hm)
    (magnitude_uniformlyNonpretentious hf hd)

lemma prefixAverage_translation_bound {f : ℕ → ℂ} (hf : OneBounded f) (h N : ℕ) :
    ‖prefixAverage (fun n => f (n + h)) N - prefixAverage f N‖ ≤
      (N : ℝ)⁻¹ * (2 * (h : ℝ)) := by
  simp only [prefixAverage, ← mul_sub, norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
  simpa only [mul_one] using SourceRoughFourier.prefix_translation_bound f N h 1 hf

lemma translation_mean_error_tendsto {f : ℕ → ℂ} (hf : OneBounded f) (h : ℕ) :
    Tendsto (fun N => prefixAverage (fun n => f (n + h)) N - prefixAverage f N)
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * (2 * (h : ℝ))) atTop (nhds 0) := by
    simpa using hinv.mul_const (2 * (h : ℝ))
  exact squeeze_zero (fun N => norm_nonneg _) (prefixAverage_translation_bound hf h) hb

theorem prefixAverage_translation_tendsto {f : ℕ → ℂ} (hf : OneBounded f)
    (hmean : Tendsto (prefixAverage f) atTop (nhds 0)) (h : ℕ) :
    Tendsto (prefixAverage (fun n => f (n + h))) atTop (nhds 0) := by
  have ht := (translation_mean_error_tendsto hf h).add hmean
  simpa only [sub_add_cancel, zero_add] using ht

lemma sum_magnitude_norm (f : ℕ → ℂ) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, magnitude f n‖ = ∑ n ∈ Finset.Icc 1 N, ‖f n‖ := by
  have he : (∑ n ∈ Finset.Icc 1 N, magnitude f n) =
      ((∑ n ∈ Finset.Icc 1 N, ‖f n‖ : ℝ) : ℂ) := by
    simp [magnitude]
  rw [he, Complex.norm_real, Real.norm_of_nonneg]
  exact Finset.sum_nonneg (fun n _ => norm_nonneg _)

lemma prefixAverage_magnitude_norm (f : ℕ → ℂ) (N : ℕ) :
    ‖prefixAverage (magnitude f) N‖ = (N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, ‖f n‖ := by
  rw [prefixAverage, norm_mul, norm_inv, Complex.norm_natCast, sum_magnitude_norm]

theorem absolute_defect_mean_zero {f : ℕ → ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hd : ¬ Summable (absPrimeDefect f)) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, ‖f n‖)
      atTop (nhds 0) := by
  simpa only [norm_zero, prefixAverage_magnitude_norm] using (magnitude_mean_zero hf hm hd).norm

lemma shiftAverage_comm (f g : ℕ → ℂ) (a b : ℕ) :
    shiftAverage f g a b = shiftAverage g f b a := by
  funext N
  simp only [shiftAverage, mul_comm (f _) (g _)]

lemma shiftAverage_norm_le_magnitude_mean {f g : ℕ → ℂ} (hg : OneBounded g)
    (a b N : ℕ) :
    ‖shiftAverage f g a b N‖ ≤ ‖prefixAverage (fun n => magnitude f (n + a)) N‖ := by
  have he : (fun n => magnitude f (n + a)) = magnitude (fun n => f (n + a)) := rfl
  rw [he, prefixAverage_magnitude_norm]
  simp only [shiftAverage, norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hg _)

theorem shiftAverage_of_divergent_defect {f g : ℕ → ℂ}
    (hf : OneBounded f) (hg : OneBounded g) (hm : Multiplicative f)
    (hd : ¬ Summable (absPrimeDefect f)) (a b : ℕ) :
    Tendsto (shiftAverage f g a b) atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht := prefixAverage_translation_tendsto (magnitude_oneBounded hf)
    (magnitude_mean_zero hf hm hd) a
  exact squeeze_zero (fun N => norm_nonneg _)
    (shiftAverage_norm_le_magnitude_mean hg a b) (by simpa using ht.norm)

theorem divergent_absolute_defect_correlation {f g : ℕ → ℂ}
    (hf : OneBounded f) (hg : OneBounded g) (hmf : Multiplicative f) (hmg : Multiplicative g)
    (hd : ¬ Summable (absPrimeDefect f) ∨ ¬ Summable (absPrimeDefect g)) (a b : ℕ) :
    Tendsto (shiftAverage f g a b) atTop (nhds 0) := by
  rcases hd with hd | hd
  · exact shiftAverage_of_divergent_defect hf hg hmf hd a b
  · simpa only [shiftAverage_comm f g a b] using
      shiftAverage_of_divergent_defect hg hf hmg hd b a

lemma positive_zero_of_zero_at_one {f : ℕ → ℂ} (hm : Multiplicative f) (hz : f 1 = 0) :
    ∀ n, 0 < n → f n = 0 := by
  rcases Completion.one_or_zero hm with h1 | hzero
  · exact False.elim (zero_ne_one (hz.symm.trans h1))
  · exact hzero

theorem shiftAverage_of_zero_at_one {f g : ℕ → ℂ}
    (hm : Multiplicative f) (hz : f 1 = 0) (a b : ℕ) :
    Tendsto (shiftAverage f g a b) atTop (nhds 0) := by
  have he : shiftAverage f g a b = fun _ => 0 := by
    funext N
    unfold shiftAverage
    have hs : (∑ n ∈ Finset.Icc 1 N, f (n + a) * g (n + b)) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      rw [positive_zero_of_zero_at_one hm hz (n + a) (by have := (Finset.mem_Icc.mp hn).1; omega)]
      exact zero_mul _
    rw [hs, mul_zero]
  rw [he]
  exact tendsto_const_nhds

theorem zero_at_one_correlation {f g : ℕ → ℂ}
    (hmf : Multiplicative f) (hmg : Multiplicative g)
    (hz : f 1 = 0 ∨ g 1 = 0) (a b : ℕ) :
    Tendsto (shiftAverage f g a b) atTop (nhds 0) := by
  rcases hz with hz | hz
  · exact shiftAverage_of_zero_at_one hmf hz a b
  · simpa only [shiftAverage_comm f g a b] using shiftAverage_of_zero_at_one hmg hz b a

theorem shiftAverage_translation_error_tendsto {f g : ℕ → ℂ}
    (hf : OneBounded f) (hg : OneBounded g) {a b : ℕ} (hab : a ≤ b) :
    Tendsto (fun N => shiftAverage f g a b N - shiftAverage f g 0 (b-a) N)
      atTop (nhds 0) := by
  have hb : OneBounded (fun n => f n * g (n + (b-a))) := by
    intro n
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hg _) (norm_nonneg _)).trans (by simpa using hf n)
  have ht := translation_mean_error_tendsto hb a
  simpa only [prefixAverage, shiftAverage, Nat.add_zero, Nat.add_assoc,
    Nat.add_sub_of_le hab] using ht

theorem positive_gap_of_failure {f g : ℕ → ℂ}
    (hf : OneBounded f) (hg : OneBounded g) {a b : ℕ} (hab : a ≠ b)
    (hfail : ¬ Tendsto (shiftAverage f g a b) atTop (nhds 0)) :
    (a < b ∧ ¬ Tendsto (shiftAverage f g 0 (b-a)) atTop (nhds 0)) ∨
      (b < a ∧ ¬ Tendsto (shiftAverage g f 0 (a-b)) atTop (nhds 0)) := by
  rcases lt_or_gt_of_ne hab with hab | hba
  · refine Or.inl ⟨hab, ?_⟩
    intro ht
    have hc := (shiftAverage_translation_error_tendsto hf hg hab.le).add ht
    exact hfail (by simpa only [sub_add_cancel, zero_add] using hc)
  · refine Or.inr ⟨hba, ?_⟩
    intro ht
    have hc := (shiftAverage_translation_error_tendsto hg hf hba.le).add ht
    have hc' : Tendsto (shiftAverage g f b a) atTop (nhds 0) := by
      simpa only [sub_add_cancel, zero_add] using hc
    exact hfail (by simpa only [shiftAverage_comm g f b a] using hc')

theorem normalized_finite_defects_of_failure {f g : ℕ → ℂ}
    (hf : OneBounded f) (hg : OneBounded g) (hmf : Multiplicative f) (hmg : Multiplicative g)
    (a b : ℕ) (hfail : ¬ Tendsto (shiftAverage f g a b) atTop (nhds 0)) :
    f 1 = 1 ∧ g 1 = 1 ∧ Summable (absPrimeDefect f) ∧ Summable (absPrimeDefect g) := by
  have hf1 : f 1 = 1 := by
    rcases Completion.one_or_zero hmf with h1 | hz
    · exact h1
    · exact False.elim (hfail (zero_at_one_correlation hmf hmg
        (Or.inl (hz 1 (by norm_num))) a b))
  have hg1 : g 1 = 1 := by
    rcases Completion.one_or_zero hmg with h1 | hz
    · exact h1
    · exact False.elim (hfail (zero_at_one_correlation hmf hmg
        (Or.inr (hz 1 (by norm_num))) a b))
  refine ⟨hf1, hg1, ?_, ?_⟩
  · by_contra hd
    exact hfail (divergent_absolute_defect_correlation hf hg hmf hmg (Or.inl hd) a b)
  · by_contra hd
    exact hfail (divergent_absolute_defect_correlation hf hg hmf hmg (Or.inr hd) a b)

theorem biased_sequence_of_failure (f g : ℕ → ℂ) (h : ℕ)
    (hfail : ¬ Tendsto (shiftAverage f g 0 h) atTop (nhds 0)) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ ∃ Ns : ℕ → ℕ, Tendsto Ns atTop atTop ∧
      ∀ j, 0 < Ns j ∧ γ * (Ns j : ℝ) ≤
        ‖∑ n ∈ Finset.Icc 1 (Ns j), f n * g (n+h)‖ := by
  have hbad : ∃ ε : ℝ, 0 < ε ∧ ∃ᶠ N : ℕ in atTop,
      ε ≤ ‖shiftAverage f g 0 h N‖ := by
    contrapose! hfail
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    simpa only [_root_.dist_zero_right] using hfail ε hε
  obtain ⟨ε, hε, hbad⟩ := hbad
  let γ := min ε 1
  have hboth : ∃ᶠ N : ℕ in atTop, 0 < N ∧ γ ≤ ‖shiftAverage f g 0 h N‖ := by
    apply (hbad.and_eventually (eventually_gt_atTop (0:ℕ))).mono
    intro N hN
    exact ⟨hN.2, (min_le_left ε 1).trans hN.1⟩
  obtain ⟨Ns, hNs, hbound⟩ := exists_seq_forall_of_frequently hboth
  refine ⟨γ, lt_min hε (by norm_num), min_le_right ε 1, Ns, hNs, ?_⟩
  intro j
  refine ⟨(hbound j).1, ?_⟩
  have hn : (0:ℝ) < Ns j := by exact_mod_cast (hbound j).1
  have hb := (hbound j).2
  simp only [shiftAverage, Nat.add_zero, norm_mul, norm_inv, Complex.norm_natCast,
    mul_comm ((Ns j : ℝ)⁻¹), ← div_eq_mul_inv] at hb
  exact (le_div_iff₀ hn).mp hb

end OrdinaryCorrelations

end

end OAI
