import OAI.Probability.Renewal.Definitions

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace HoneycombLocal

def latticeChar (p : PMF ℕ) (t : ℝ) : ℂ :=
  ∫ j, Complex.exp (((j : ℝ) * t : ℝ) * Complex.I) ∂p.toMeasure

lemma integrable_lattice_exp (p : PMF ℕ) (t : ℝ) :
    Integrable (fun j : ℕ => Complex.exp (((j : ℝ) * t : ℝ) * Complex.I)) p.toMeasure := by
  apply Integrable.of_bound (Measurable.of_discrete.aestronglyMeasurable) 1
  exact Filter.Eventually.of_forall (fun j => by rw [Complex.norm_exp_ofReal_mul_I])

lemma latticeChar_eq_charFun (p : PMF ℕ) (t : ℝ) :
    latticeChar p t = charFun (Measure.map (fun j : ℕ => (j : ℝ)) p.toMeasure) t := by
  rw [charFun_apply, integral_map Measurable.of_discrete.aemeasurable]
  · simp only [latticeChar, RCLike.inner_apply, conj_trivial, mul_comm]
  · exact (by fun_prop : Continuous (fun x : ℝ => Complex.exp ((inner ℝ x t : ℝ) * Complex.I))).aestronglyMeasurable

lemma norm_latticeChar_le_one (p : PMF ℕ) (t : ℝ) : ‖latticeChar p t‖ ≤ 1 := by
  rw [latticeChar_eq_charFun]
  exact norm_charFun_le_one t

lemma continuous_latticeChar (p : PMF ℕ) : Continuous (latticeChar p) := by
  have he : latticeChar p = charFun (Measure.map (fun j : ℕ => (j : ℝ)) p.toMeasure) :=
    funext (latticeChar_eq_charFun p)
  rw [he]
  exact continuous_charFun

lemma integral_lattice_exp (z : ℤ) :
    (∫ t : ℝ in -Real.pi..Real.pi,
      Complex.exp (((z : ℝ) * t : ℝ) * Complex.I)) =
      if z = 0 then (2 * Real.pi : ℂ) else 0 := by
  by_cases hz : z = 0
  · subst z
    simp [intervalIntegral.integral_const]
    ring
  · rw [ite_eq_right hz]
    have hz' : (z : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hz) Complex.I_ne_zero
    have heq : (fun t : ℝ => Complex.exp (((z : ℝ) * t : ℝ) * Complex.I)) =
        fun t : ℝ => Complex.exp (((z : ℂ) * Complex.I) * t) := by
      ext t; congr 1; push_cast; ring
    rw [heq, integral_exp_mul_complex hz']
    have he : Complex.exp (((z : ℂ) * Complex.I) * Real.pi) =
        Complex.exp (((z : ℂ) * Complex.I) * (-Real.pi)) := by
      have e1 : ((z : ℂ) * Complex.I) * Real.pi = ((z : ℝ) * Real.pi : ℝ) * Complex.I := by push_cast; ring
      have e2 : ((z : ℂ) * Complex.I) * (-Real.pi) = -((z : ℝ) * Real.pi : ℝ) * Complex.I := by push_cast; ring
      rw [e1, e2, Complex.exp_mul_I, Complex.exp_mul_I]
      have hs : Complex.sin (((z : ℝ) * Real.pi : ℝ) : ℂ) = 0 := by
        rw [← Complex.ofReal_sin, Real.sin_int_mul_pi]; rfl
      simp only [Complex.cos_neg, Complex.sin_neg, hs, zero_mul, add_zero, neg_zero]
    simp only [Complex.ofReal_neg]
    rw [he, sub_self, zero_div]

lemma lattice_inversion (p : PMF ℕ) (m : ℕ) :
    (∫ t : ℝ in -Real.pi..Real.pi,
      latticeChar p t * Complex.exp (-((m : ℝ) * t : ℝ) * Complex.I)) =
      (2 * Real.pi : ℂ) * ((p m).toReal : ℂ) := by
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  let ν : Measure ℝ := volume.restrict (Ioc (-Real.pi) Real.pi)
  let f : ℝ → ℕ → ℂ := fun t j => Complex.exp ((((j : ℝ) - m) * t : ℝ) * Complex.I)
  have hi : Integrable (Function.uncurry f) (ν.prod p.toMeasure) := by
    refine Integrable.of_bound ?_ 1 ?_
    · have : Continuous (Function.uncurry f) := by dsimp [f, Function.uncurry]; fun_prop
      exact this.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun x => by dsimp [f, Function.uncurry]; rw [Complex.norm_exp_ofReal_mul_I])
  have hpoint (t : ℝ) : latticeChar p t * Complex.exp (-((m : ℝ) * t : ℝ) * Complex.I) =
      ∫ j, f t j ∂p.toMeasure := by
    rw [latticeChar, ← integral_mul_const]
    congr 1; ext j
    dsimp [f]
    rw [← Complex.exp_add]
    congr 1
    push_cast; ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_of_le hpi]
  change (∫ t, ∫ j, f t j ∂p.toMeasure ∂ν) = _
  rw [integral_integral_swap hi]
  have hinner (j : ℕ) : (∫ t, f t j ∂ν) =
      ({m} : Set ℕ).indicator (fun _ => (2 * Real.pi : ℂ)) j := by
    change (∫ t in Ioc (-Real.pi) Real.pi, f t j) = _
    rw [← intervalIntegral.integral_of_le hpi]
    have he : (fun t => f t j) = fun t : ℝ =>
        Complex.exp ((((((j : ℤ) - m) : ℤ) : ℝ) * t : ℝ) * Complex.I) := by
      ext t; dsimp [f]; push_cast; rfl
    rw [he, integral_lattice_exp]
    by_cases hj : j = m
    · subst j; simp
    · have : (j : ℤ) - m ≠ 0 := by omega
      simp [this, hj]
  simp_rw [hinner]
  rw [integral_indicator (measurableSet_singleton _), integral_singleton]
  simp [Measure.real, p.toMeasure_apply_singleton m (measurableSet_singleton _), mul_comm]

lemma two_copy_defect (p : PMF ℕ) (t : ℝ) :
    (∫ z : ℕ × ℕ, 1 - Real.cos (((z.1 : ℝ) - z.2) * t)
      ∂p.toMeasure.prod p.toMeasure) = 1 - ‖latticeChar p t‖ ^ 2 := by
  let e : ℕ → ℂ := fun j => Complex.exp (((j : ℝ) * t : ℝ) * Complex.I)
  let d : ℕ × ℕ → ℂ := fun z => Complex.exp ((((z.1 : ℝ) - z.2) * t : ℝ) * Complex.I)
  have hi : Integrable d (p.toMeasure.prod p.toMeasure) := by
    refine Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall (fun z => by dsimp [d]; rw [Complex.norm_exp_ofReal_mul_I])
  have heq (z : ℕ × ℕ) : d z = e z.1 * star (e z.2) := by
    dsimp [e, d]
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  have hp : (∫ z, d z ∂p.toMeasure.prod p.toMeasure) =
      latticeChar p t * star (latticeChar p t) := by
    simp_rw [heq]
    rw [integral_prod_mul e (fun j => star (e j))]
    change (∫ x, e x ∂p.toMeasure) * (∫ y, (starRingEnd ℂ) (e y) ∂p.toMeasure) = _
    rw [integral_conj]
    rfl
  have hr (z : ℕ × ℕ) : (d z).re = Real.cos (((z.1 : ℝ) - z.2) * t) := by
    simp [d, Complex.exp_re]
  have hcint : Integrable (fun z : ℕ × ℕ => Real.cos (((z.1 : ℝ) - z.2) * t))
      (p.toMeasure.prod p.toMeasure) := by
    simpa only [RCLike.re_to_complex, hr] using hi.re
  have hc : (∫ z : ℕ × ℕ, Real.cos (((z.1 : ℝ) - z.2) * t)
      ∂p.toMeasure.prod p.toMeasure) = ‖latticeChar p t‖ ^ 2 := by
    simp_rw [← hr]
    have hreal : (∫ z, (d z).re ∂p.toMeasure.prod p.toMeasure) =
        (∫ z, d z ∂p.toMeasure.prod p.toMeasure).re := by
      simpa only [RCLike.re_to_complex] using integral_re hi
    rw [hreal, hp]
    change (latticeChar p t * (starRingEnd ℂ) (latticeChar p t)).re = _
    rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [integral_sub (integrable_const 1) hcint, hc]
  simp

lemma integrable_two_copy_defect (p : PMF ℕ) (t : ℝ) :
    Integrable (fun z : ℕ × ℕ => 1 - Real.cos (((z.1 : ℝ) - z.2) * t))
      (p.toMeasure.prod p.toMeasure) := by
  refine Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable 2 ?_
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
  linarith [Real.neg_one_le_cos (((z.1 : ℝ) - z.2) * t)]

lemma rectangle_defect_bound (p : PMF ℕ) (t r : ℝ) (s b : Set ℕ)
    (hlower : ∀ j ∈ s, ∀ l ∈ b, r ≤ 1 - Real.cos (((j : ℝ) - l) * t)) :
    p.toMeasure.real s * p.toMeasure.real b * r ≤ 1 - ‖latticeChar p t‖ ^ 2 := by
  let μ := p.toMeasure.prod p.toMeasure
  have hi := integrable_two_copy_defect p t
  have hpos : 0 ≤ fun z : ℕ × ℕ => 1 - Real.cos (((z.1 : ℝ) - z.2) * t) :=
    fun z => sub_nonneg.mpr (Real.cos_le_one _)
  calc
    p.toMeasure.real s * p.toMeasure.real b * r = ∫ z : ℕ × ℕ in s ×ˢ b, r ∂μ := by
      simp [Measure.real, Measure.prod_prod, ENNReal.toReal_mul, μ]
    _ ≤ ∫ z : ℕ × ℕ in s ×ˢ b, 1 - Real.cos (((z.1 : ℝ) - z.2) * t) ∂μ := by
      apply setIntegral_mono_on (integrable_const r) hi.integrableOn MeasurableSet.of_discrete
      intro z hz
      exact hlower z.1 hz.1 z.2 hz.2
    _ ≤ ∫ z : ℕ × ℕ, 1 - Real.cos (((z.1 : ℝ) - z.2) * t) ∂μ :=
      setIntegral_le_integral hi (Filter.Eventually.of_forall hpos)
    _ = 1 - ‖latticeChar p t‖ ^ 2 := two_copy_defect p t

lemma support_diff_cos_eq_one (p : PMF ℕ) {t : ℝ} (hnorm : ‖latticeChar p t‖ = 1)
    {j l : ℕ} (hj : j ∈ p.support) (hl : l ∈ p.support) :
    Real.cos (((j : ℝ) - l) * t) = 1 := by
  have h := rectangle_defect_bound p t (1 - Real.cos (((j : ℝ) - l) * t)) {j} {l}
    (by intro x hx y hy; rw [mem_singleton_iff.mp hx, mem_singleton_iff.mp hy])
  have hj' : 0 < (p j).toReal := ENNReal.toReal_pos (p.mem_support_iff j |>.mp hj) (p.apply_ne_top j)
  have hl' : 0 < (p l).toReal := ENNReal.toReal_pos (p.mem_support_iff l |>.mp hl) (p.apply_ne_top l)
  simp only [Measure.real, p.toMeasure_apply_singleton _ (measurableSet_singleton _), hnorm,
    one_pow, sub_self] at h
  have hprod : 0 < (p j).toReal * (p l).toReal := mul_pos hj' hl'
  have hc : 0 ≤ 1 - Real.cos (((j : ℝ) - l) * t) := sub_nonneg.mpr (Real.cos_le_one _)
  nlinarith

lemma exp_of_cos_eq_one {x : ℝ} (h : Real.cos x = 1) :
    Complex.exp ((x : ℂ) * Complex.I) = 1 := by
  rcases (Real.cos_eq_one_iff x).mp h with ⟨n, hn⟩
  apply Complex.exp_eq_one_iff.mpr
  refine ⟨n, ?_⟩
  rw [← hn]
  push_cast
  ring

lemma norm_latticeChar_lt_one (p : PMF ℕ) (hspan : SpanOne p) {t : ℝ}
    (ht : t ≠ 0) (htpi : |t| ≤ Real.pi) : ‖latticeChar p t‖ < 1 := by
  refine lt_of_le_of_ne (norm_latticeChar_le_one p t) ?_
  intro hnorm
  have h1 : (1 : ℤ) ∈ AddSubgroup.closure
      {z : ℤ | ∃ j ∈ p.support, ∃ k ∈ p.support, z = (j : ℤ) - k} := by
    rw [hspan]
    trivial
  have hexp : Complex.exp ((((1 : ℤ) : ℝ) * t : ℝ) * Complex.I) = 1 := by
    refine AddSubgroup.closure_induction (p := fun (z : ℤ) _ =>
      Complex.exp (((z : ℝ) * t : ℝ) * Complex.I) = 1) ?_ ?_ ?_ ?_ h1
    · intro z hz
      rcases hz with ⟨j, hj, l, hl, rfl⟩
      simpa only [Int.cast_sub, Int.cast_natCast] using
        exp_of_cos_eq_one (support_diff_cos_eq_one p hnorm hj hl)
    · simp
    · intro x y hx hy hx' hy'
      have heq : ((((x + y : ℤ) : ℝ) * t : ℝ) : ℂ) * Complex.I =
          (((x : ℝ) * t : ℝ) : ℂ) * Complex.I + (((y : ℝ) * t : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [heq, Complex.exp_add, hx', hy', one_mul]
    · intro x hx hx'
      have heq : ((((-x : ℤ) : ℝ) * t : ℝ) : ℂ) * Complex.I =
          -((((x : ℝ) * t : ℝ) : ℂ) * Complex.I) := by push_cast; ring
      rw [heq, Complex.exp_neg, hx', inv_one]
  have hcos : Real.cos t = 1 := by
    have := congrArg Complex.re hexp
    simpa only [Int.cast_one, one_mul, Complex.exp_ofReal_mul_I_re, Complex.one_re] using this
  have hb := abs_le.mp htpi
  exact ht ((Real.cos_eq_one_iff_of_lt_of_lt
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).mp hcos)

lemma lattice_spectral_gap (p : PMF ℕ) (hspan : SpanOne p) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ t : ℝ, δ ≤ |t| → |t| ≤ Real.pi → ‖latticeChar p t‖ ≤ ρ := by
  by_cases hdpi : δ ≤ Real.pi
  · let s : Set ℝ := {t | δ ≤ |t|} ∩ Icc (-Real.pi) Real.pi
    have hs : IsCompact s := isCompact_Icc.inter_left (isClosed_le continuous_const continuous_abs)
    have hne : s.Nonempty := ⟨Real.pi, by simp [s, abs_of_pos Real.pi_pos, hdpi, Real.pi_pos.le]⟩
    obtain ⟨t, ht, hmax⟩ := hs.exists_isMaxOn hne (continuous_latticeChar p |>.norm.continuousOn)
    refine ⟨‖latticeChar p t‖, norm_nonneg _, ?_, ?_⟩
    · apply norm_latticeChar_lt_one p hspan
      · intro h; subst t; have := ht.1; simp only [abs_zero, mem_ofPred_eq] at this; linarith
      · exact abs_le.mpr ht.2
    · intro y hy hy'
      exact hmax ⟨hy, abs_le.mp hy'⟩
  · refine ⟨0, le_rfl, zero_lt_one, ?_⟩
    intro t ht ht'
    exact False.elim (hdpi (ht.trans ht'))

end HoneycombLocal

end

end OAI
