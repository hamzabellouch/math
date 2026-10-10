import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Energy paid by a line crossing a barrier

A barrier that is zero at an end of `[-L, L]` and equals one somewhere
on the segment has squared derivative integral at least `1 / (2 * L)`.
This follows from the fundamental theorem of calculus and the integral
Cauchy–Schwarz inequality.

Both absolutely continuous and `C¹` restrictions satisfy this estimate.
Fubini's theorem gives the rectangular energy lower bound when horizontal
slices are almost everywhere absolutely continuous.
-/

open MeasureTheory Set

namespace CircleDomainRigidity

/-- Cauchy–Schwarz against the constant function on a finite interval,
written without square roots. -/
theorem integral_sq_le_length_mul_integral_sq {g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hg : IntervalIntegrable g volume a b)
    (hg2 : IntervalIntegrable (fun x => g x ^ 2) volume a b) :
    (∫ x in a..b, g x) ^ 2 ≤ (b - a) * (∫ x in a..b, g x ^ 2) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  let J := ∫ x in a..b, g x
  have hpoly : (fun x => ((b - a) * g x - J) ^ 2) =
      (fun x => (b - a) ^ 2 * g x ^ 2 - (2 * (b - a) * J) * g x + J ^ 2) := by
    funext x
    ring
  have hnonneg := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab.le
    (fun x => sq_nonneg ((b - a) * g x - J))
  rw [hpoly, intervalIntegral.integral_add
      ((hg2.const_mul _).sub (hg.const_mul _)) intervalIntegrable_const,
    intervalIntegral.integral_sub (hg2.const_mul _) (hg.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul] at hnonneg
  have hmul : (b - a) * J ^ 2 ≤
      (b - a) * ((b - a) * (∫ x in a..b, g x ^ 2)) := by
    dsimp [J] at *
    nlinarith
  exact le_of_mul_le_mul_left hmul (sub_pos.mpr hab)

/-- A continuous restriction with endpoint value zero and
an interior or endpoint value one pays at least reciprocal interval length
in squared derivative energy. The derivative need only exist in the open
interval, and both integrability assumptions are ordinary FTC hypotheses. -/
theorem line_payment_of_hasDerivAt {f d : ℝ → ℝ} {a b c : ℝ}
    (hc : c ∈ Icc a b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (d x) x)
    (hi : IntervalIntegrable d volume a b)
    (hi2 : IntervalIntegrable (fun x => d x ^ 2) volume a b)
    (ha : f a = 0) (hcone : f c = 1) :
    1 ≤ (b - a) * (∫ x in a..b, d x ^ 2) := by
  have hsub : uIcc a c ⊆ uIcc a b :=
    uIcc_subset_uIcc_left (by simpa [uIcc_of_le (hc.1.trans hc.2)] using hc)
  have hiac := hi.mono_set hsub
  have hi2ac := hi2.mono_set hsub
  have hFTC : (∫ x in a..c, d x) = f c - f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hc.1
      (hf.mono (Icc_subset_Icc le_rfl hc.2))
      (fun x hx => hd x ⟨hx.1, lt_of_lt_of_le hx.2 hc.2⟩) hiac
  have hmono : (∫ x in a..c, d x ^ 2) ≤ ∫ x in a..b, d x ^ 2 :=
    intervalIntegral.integral_mono_interval le_rfl hc.1 hc.2
      (Filter.Eventually.of_forall (fun x => sq_nonneg (d x))) hi2
  have henergy : 0 ≤ ∫ x in a..b, d x ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall (hc.1.trans hc.2)
      (fun x => sq_nonneg (d x))
  calc
    1 = (∫ x in a..c, d x) ^ 2 := by rw [hFTC, hcone, ha]; norm_num
    _ ≤ (c - a) * (∫ x in a..c, d x ^ 2) :=
      integral_sq_le_length_mul_integral_sq hc.1 hiac hi2ac
    _ ≤ (c - a) * (∫ x in a..b, d x ^ 2) :=
      mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hc.1)
    _ ≤ (b - a) * (∫ x in a..b, d x ^ 2) :=
      mul_le_mul_of_nonneg_right (sub_le_sub_right hc.2 a) henergy

/-- The smooth-barrier specialization needs no separate integrability
hypotheses: continuity of the derivative on a compact interval supplies
them. -/
theorem line_payment_of_contDiff {f : ℝ → ℝ} {a b c : ℝ}
    (hf : ContDiff ℝ 1 f) (hc : c ∈ Icc a b)
    (ha : f a = 0) (hcone : f c = 1) :
    1 ≤ (b - a) * (∫ x in a..b, deriv f x ^ 2) := by
  exact line_payment_of_hasDerivAt hc hf.continuous.continuousOn
    (fun x _ => (hf.differentiable_one x).hasDerivAt)
    (hf.continuous_deriv_one.intervalIntegrable a b)
    ((hf.continuous_deriv_one.pow 2).intervalIntegrable a b) ha hcone

/-- The `1 / (2L)` payment of a smooth barrier on a horizontal segment in
the supporting square `[-L,L]²`. Only the left endpoint value is needed. -/
theorem line_payment_on_symmetric_interval {f : ℝ → ℝ} {L c : ℝ}
    (hL : 0 < L) (hf : ContDiff ℝ 1 f) (hc : c ∈ Icc (-L) L)
    (ha : f (-L) = 0) (hcone : f c = 1) :
    1 / (2 * L) ≤ ∫ x in (-L)..L, deriv f x ^ 2 := by
  apply (div_le_iff₀ (mul_pos (by norm_num) hL)).mpr
  have h := line_payment_of_contDiff hf hc ha hcone
  nlinarith

/-- The actual absolutely continuous case of the line-payment estimate.
Absolute continuity supplies the integrable derivative and its fundamental
theorem of calculus; only square-integrability is an extra energy hypothesis. -/
theorem line_payment_of_absolutelyContinuous {f : ℝ → ℝ} {a b c : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hc : c ∈ Icc a b)
    (hi2 : IntervalIntegrable (fun x => deriv f x ^ 2) volume a b)
    (ha : f a = 0) (hcone : f c = 1) :
    1 ≤ (b - a) * (∫ x in a..b, deriv f x ^ 2) := by
  have hsub : uIcc a c ⊆ uIcc a b :=
    uIcc_subset_uIcc_left (by simpa [uIcc_of_le (hc.1.trans hc.2)] using hc)
  have hiac := hf.intervalIntegrable_deriv.mono_set hsub
  have hi2ac := hi2.mono_set hsub
  have hFTC := (hf.mono hsub).integral_deriv_eq_sub
  have hmono : (∫ x in a..c, deriv f x ^ 2) ≤ ∫ x in a..b, deriv f x ^ 2 :=
    intervalIntegral.integral_mono_interval le_rfl hc.1 hc.2
      (Filter.Eventually.of_forall (fun x => sq_nonneg (deriv f x))) hi2
  have henergy : 0 ≤ ∫ x in a..b, deriv f x ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall (hc.1.trans hc.2)
      (fun x => sq_nonneg (deriv f x))
  calc
    1 = (∫ x in a..c, deriv f x) ^ 2 := by rw [hFTC, hcone, ha]; norm_num
    _ ≤ (c - a) * (∫ x in a..c, deriv f x ^ 2) :=
      integral_sq_le_length_mul_integral_sq hc.1 hiac hi2ac
    _ ≤ (c - a) * (∫ x in a..b, deriv f x ^ 2) :=
      mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hc.1)
    _ ≤ (b - a) * (∫ x in a..b, deriv f x ^ 2) :=
      mul_le_mul_of_nonneg_right (sub_le_sub_right hc.2 a) henergy

/-- The sharp form needed on each absolutely continuous horizontal slice
of a Sobolev barrier supported in the square `[-L,L]²`. -/
theorem line_payment_on_symmetric_interval_of_absolutelyContinuous
    {f : ℝ → ℝ} {L c : ℝ} (hL : 0 < L)
    (hf : AbsolutelyContinuousOnInterval f (-L) L) (hc : c ∈ Icc (-L) L)
    (hi2 : IntervalIntegrable (fun x => deriv f x ^ 2) volume (-L) L)
    (ha : f (-L) = 0) (hcone : f c = 1) :
    1 / (2 * L) ≤ ∫ x in (-L)..L, deriv f x ^ 2 := by
  apply (div_le_iff₀ (mul_pos (by norm_num) hL)).mpr
  have h := line_payment_of_absolutelyContinuous hf hc hi2 ha hcone
  nlinarith

/-- Integrating line payment over a transverse interval gives the energy
lower bound `(b-a)/(2L)`. The hypotheses are the actual ACL slice conditions
and integrability of the squared horizontal derivative on the rectangle.
Fubini supplies square-integrability on almost every slice and integrability
of the resulting slice energies. Coordinates are written `(y,x)`. -/
theorem integrated_line_payment_of_absolutelyContinuous
    {v : ℝ → ℝ → ℝ} {L a b : ℝ} (hL : 0 < L) (hab : a ≤ b)
    (hEnergy : Integrable (fun p : ℝ × ℝ => deriv (v p.1) p.2 ^ 2)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc (-L) L))))
    (hSlices : ∀ᵐ y ∂volume.restrict (Ioc a b),
      AbsolutelyContinuousOnInterval (v y) (-L) L ∧ v y (-L) = 0 ∧
        ∃ c ∈ Icc (-L) L, v y c = 1) :
    (b - a) / (2 * L) ≤
      ∫ p : ℝ × ℝ, deriv (v p.1) p.2 ^ 2
        ∂((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc (-L) L))) := by
  let : IsFiniteMeasure (volume.restrict (Ioc a b)) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  have hLL : -L ≤ L := by linarith
  have hbound : ∀ᵐ y ∂volume.restrict (Ioc a b),
      1 / (2 * L) ≤ ∫ x in Ioc (-L) L, deriv (v y) x ^ 2 := by
    filter_upwards [hSlices, hEnergy.prod_right_ae] with y hy hiy
    obtain ⟨hAC, hzero, c, hc, hone⟩ := hy
    have hi2 : IntervalIntegrable (fun x => deriv (v y) x ^ 2) volume (-L) L :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hLL).mpr hiy
    simpa only [intervalIntegral.integral_of_le hLL] using
      line_payment_on_symmetric_interval_of_absolutelyContinuous hL hAC hc hi2 hzero hone
  calc
    (b - a) / (2 * L) = ∫ _y in Ioc a b, (1 / (2 * L) : ℝ) := by
      simp [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
        div_eq_mul_inv]
    _ ≤ ∫ y in Ioc a b, ∫ x in Ioc (-L) L, deriv (v y) x ^ 2 :=
      integral_mono_ae (integrable_const _) hEnergy.integral_prod_left hbound
    _ = _ := (integral_prod _ hEnergy).symm

end CircleDomainRigidity

end OAI
