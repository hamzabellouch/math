import OAI.Analysis.KadisonKastler.ScalarBoundaryMean

namespace OAI

/-! # Conjugation preservation of the scalar boundary mean

Positivity preserves real sections after adding a sufficiently large
constant. Applying this to the real and imaginary parts proves that the
complex-linear scalar mean commutes with conjugation.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {D G : Type*} [MeasurableSpace D] {μ : Measure D}
  [TopologicalSpace G] [DiscreteTopology G] [IsFiniteMeasure μ]

/-- Conjugating a scalar L-infinity class does not enlarge its norm. -/
theorem scalarInfinity_norm_star_le (f : ScalarLInfinity μ) : ‖star f‖ ≤ ‖f‖ := by
  have hb : ∀ᵐ x ∂μ, ‖(star f : ScalarLInfinity μ) x‖ ≤ ‖f‖ := by
    filter_upwards [Lp.coeFn_star f, scalarInfinity_ae_norm_le f] with x hx hf
    simpa only [Pi.star_apply, hx, norm_star] using hf
  simpa using Lp.norm_le_of_ae_bound (norm_nonneg f) hb

theorem scalarInfinity_norm_star (f : ScalarLInfinity μ) : ‖star f‖ = ‖f‖ :=
  le_antisymm (scalarInfinity_norm_star_le f)
    (by simpa only [star_star] using scalarInfinity_norm_star_le (star f))

/-- Coordinatewise conjugation on the bounded family of scalar sections. -/
def scalarBoundaryStar (F : G →ᵇ ScalarLInfinity μ) : G →ᵇ ScalarLInfinity μ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun g => star (F g)) ‖F‖ (fun g =>
      (scalarInfinity_norm_star_le (F g)).trans (F.norm_coe_le_norm g))

@[simp]
theorem scalarBoundaryStar_apply (F : G →ᵇ ScalarLInfinity μ) (g : G) :
    scalarBoundaryStar F g = star (F g) := rfl

theorem scalarBoundaryStar_ae (F : G →ᵇ ScalarLInfinity μ) (g : G) :
    scalarBoundaryStar F g =ᵐ[μ] fun x => star (F g x) := by
  exact (Lp.coeFn_star (F g)).mono fun x hx => by
    change (star (F g) : ScalarLInfinity μ) x = star (F g x)
    exact hx

variable [Group G] {α : NonsingularAction G D μ}

namespace ScalarBoundaryMean

variable (m : ScalarBoundaryMean α)

/-- Positivity and fixed constants imply preservation of real sections. -/
theorem map_real (F : G →ᵇ ScalarLInfinity μ)
    (hF : ∀ g, ∀ᵐ x ∂μ, (F g x).im = 0) :
    ∀ᵐ x ∂μ, (m.toCLM F x).im = 0 := by
  let b : ScalarLInfinity μ := scalarInfinityConst μ (‖F‖ : ℂ)
  have hp : ∀ g, ∀ᵐ x ∂μ,
      ((F + BoundedContinuousFunction.const G b) g x).im = 0 ∧
        0 ≤ ((F + BoundedContinuousFunction.const G b) g x).re := by
    intro g
    change ∀ᵐ x ∂μ, ((F g + b) x).im = 0 ∧ 0 ≤ ((F g + b) x).re
    filter_upwards [hF g, scalarInfinity_ae_norm_le (F g),
      Lp.coeFn_add (F g) b, scalarInfinityConst_ae (μ := μ) (‖F‖ : ℂ)]
      with x hreal hnorm hadd hb
    change b x = (‖F‖ : ℂ) at hb
    simp only [Pi.add_apply] at hadd
    rw [hadd, hb]
    constructor
    · simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using hreal
    · simp only [Complex.add_re, Complex.ofReal_re]
      have hn := hnorm.trans (F.norm_coe_le_norm g)
      have hr := (abs_le.mp (Complex.abs_re_le_norm (F g x))).1
      linarith
  have hm := m.positive (F + BoundedContinuousFunction.const G b) hp
  rw [map_add, m.fixed] at hm
  filter_upwards [hm, Lp.coeFn_add (m.toCLM F) b,
    scalarInfinityConst_ae (μ := μ) (‖F‖ : ℂ)] with x hx hadd hb
  change b x = (‖F‖ : ℂ) at hb
  simp only [Pi.add_apply] at hadd
  have hi := hx.1
  rw [hadd, hb] at hi
  simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using hi

/-- A positive complex-linear scalar boundary mean preserves conjugation. -/
theorem map_star (F : G →ᵇ ScalarLInfinity μ) :
    m.toCLM (scalarBoundaryStar F) = star (m.toCLM F) := by
  let S := scalarBoundaryStar F
  have hreal : ∀ g, ∀ᵐ x ∂μ, ((F + S) g x).im = 0 := by
    intro g
    change ∀ᵐ x ∂μ, ((F g + S g) x).im = 0
    filter_upwards [Lp.coeFn_add (F g) (S g), scalarBoundaryStar_ae F g]
      with x hadd hstar
    change S g x = star (F g x) at hstar
    simp only [Pi.add_apply] at hadd
    rw [hadd, hstar]
    simp only [Complex.add_im, Complex.star_def, Complex.conj_im, add_neg_cancel]
  have himag : ∀ g, ∀ᵐ x ∂μ, (((-Complex.I) • (F - S)) g x).im = 0 := by
    intro g
    change ∀ᵐ x ∂μ, (((-Complex.I) • (F g - S g)) x).im = 0
    filter_upwards [Lp.coeFn_smul (-Complex.I) (F g - S g),
      Lp.coeFn_sub (F g) (S g), scalarBoundaryStar_ae F g]
      with x hsmul hsub hstar
    change S g x = star (F g x) at hstar
    simp only [Pi.smul_apply] at hsmul
    simp only [Pi.sub_apply] at hsub
    rw [hsmul, hsub, hstar]
    simp only [smul_eq_mul, Complex.mul_im, Complex.neg_re, Complex.I_re,
      neg_zero, zero_mul, Complex.neg_im, Complex.I_im, Complex.sub_re,
      Complex.star_def, Complex.conj_re, sub_self, mul_zero, add_zero]
  have hsum := m.map_real (F + S) hreal
  have hdiff := m.map_real ((-Complex.I) • (F - S)) himag
  rw [map_add] at hsum
  rw [map_smul, map_sub] at hdiff
  apply Lp.ext
  filter_upwards [hsum, hdiff,
    Lp.coeFn_add (m.toCLM F) (m.toCLM S),
    Lp.coeFn_smul (-Complex.I) (m.toCLM F - m.toCLM S),
    Lp.coeFn_sub (m.toCLM F) (m.toCLM S), Lp.coeFn_star (m.toCLM F)]
      with x hsum hdiff hadd hsmul hsub hstar
  change (m.toCLM S) x = (star (m.toCLM F) : ScalarLInfinity μ) x
  simp only [Pi.add_apply] at hadd
  simp only [Pi.smul_apply] at hsmul
  simp only [Pi.sub_apply] at hsub
  rw [hadd, Complex.add_im] at hsum
  rw [hsmul, hsub] at hdiff
  simp only [smul_eq_mul, Complex.mul_im, Complex.neg_re, Complex.I_re,
    neg_zero, zero_mul, Complex.neg_im, Complex.I_im, Complex.sub_re,
    neg_one_mul, zero_add] at hdiff
  simp only [Pi.star_apply] at hstar
  rw [hstar]
  apply Complex.ext
  · simp only [Complex.star_def, Complex.conj_re]
    linarith
  · simp only [Complex.star_def, Complex.conj_im]
    linarith

end ScalarBoundaryMean

end

end KadisonKastler

end OAI
