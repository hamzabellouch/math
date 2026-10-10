import OAI.MathematicalPhysics.Boltzmann.Collision.AxialFlow
import OAI.MathematicalPhysics.Boltzmann.Collision.GaussianEstimates
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyIntegralBalance
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Order.Group.Lattice

namespace OAI

section

/-! # The scalar relative-entropy balance along characteristic paths -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem scalar_entropy_integral_balance {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (a m e R : Phase → ℝ) (r : ℝ × Phase → ℝ)
    (hm : ∀ p, 0 < m p) (he : ∀ p, 0 < e p) (hR : ∀ p, 0 ≤ R p)
    (hri : Integrable r ((volume.restrict (Icc 0 T)).prod volume))
    (hbound : ∀ᵐ p : Phase, ∀ᵐ t ∂volume.restrict (Icc 0 T),
      entropyPath a r t p ∈ Icc 0 (R p))
    (hET : Integrable (fun p => scalarRelativeEntropy (m p) (entropyPath a r T p+δ*e p)))
    (hE0 : Integrable (fun p => scalarRelativeEntropy (m p) (a p+δ*e p)))
    (hbase : Integrable (fun p => scalarRelativeEntropy (m p) (δ*e p))) (hmi : Integrable m)
    (hLi : Integrable (fun z : ℝ × Phase =>
      Real.log ((entropyPath a r z.1 z.2+δ*e z.2)/m z.2)*r z)
      ((volume.restrict (Icc 0 T)).prod volume)) :
    (∫ p : Phase, scalarRelativeEntropy (m p) (entropyPath a r T p+δ*e p))-
      (∫ p : Phase, scalarRelativeEntropy (m p) (a p+δ*e p)) =
    ∫ z : ℝ × Phase, Real.log ((entropyPath a r z.1 z.2+δ*e z.2)/m z.2)*r z
      ∂(volume.restrict (Icc 0 T)).prod volume := by
  have hAT : Integrable (fun p => regularizedEntropy (m p) (e p) δ (entropyPath a r T p)) :=
    (hET.sub hbase).add hmi
  have hA0 : Integrable (fun p => regularizedEntropy (m p) (e p) δ (a p)) :=
    (hE0.sub hbase).add hmi
  have h := entropy_integral_balance hT hδ a m e R r hm he hR hri hbound hAT hA0 hLi
  have heq : (fun p => scalarRelativeEntropy (m p) (entropyPath a r T p+δ*e p)-
      scalarRelativeEntropy (m p) (a p+δ*e p)) =
      (fun p => regularizedEntropy (m p) (e p) δ (entropyPath a r T p)-
        regularizedEntropy (m p) (e p) δ (a p)) := by
    funext p
    unfold regularizedEntropy
    ring
  calc
    _ = ∫ p : Phase, scalarRelativeEntropy (m p) (entropyPath a r T p+δ*e p)-
        scalarRelativeEntropy (m p) (a p+δ*e p) := (integral_sub hET hE0).symm
    _ = ∫ p : Phase, regularizedEntropy (m p) (e p) δ (entropyPath a r T p)-
        regularizedEntropy (m p) (e p) δ (a p) := congrArg (fun f : Phase → ℝ => ∫ p, f p) heq
    _ = _ := (integral_sub hAT hA0).trans h

end BoltzmannNonuniqueness

end

end

section

/-! # Bounded dual tests for relative entropy -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness

def entropyDual (m u s : ℝ) : ℝ := u*s-m*(Real.exp s-1)

theorem entropyDual_le {m u : ℝ} (hm : 0 < m) (hu : 0 ≤ u) (s : ℝ) :
    entropyDual m u s ≤ scalarRelativeEntropy m u := by
  by_cases hz : u = 0
  · subst u
    dsimp [entropyDual,scalarRelativeEntropy]
    nlinarith [Real.exp_pos s]
  · have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
    have hr : 0 < u/m := div_pos hup hm
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (s-Real.log (u/m))) hu
    rw [Real.exp_sub,Real.exp_log hr] at h
    have he : u*(Real.exp s/(u/m)) = m*Real.exp s := by field_simp
    rw [he] at h
    rw [scalarRelativeEntropy_eq hm]
    dsimp [entropyDual]
    nlinarith only [h]

theorem entropyDual_log_ratio {m u : ℝ} (hm : 0 < m) (hu : 0 < u) :
    entropyDual m u (Real.log (u/m)) = scalarRelativeEntropy m u := by
  rw [scalarRelativeEntropy_eq hm]
  unfold entropyDual
  rw [Real.exp_log (div_pos hu hm)]
  field_simp
  ring

theorem entropyDual_zero_tendsto (m : ℝ) :
    Tendsto (fun r : ℝ => entropyDual m 0 (-r)) atTop (𝓝 m) := by
  have h : Tendsto (fun r : ℝ => Real.exp (-r)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have ht : Tendsto (fun r : ℝ => m-m*Real.exp (-r)) atTop (𝓝 m) := by
    simpa only [mul_zero,sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => m) atTop (𝓝 m)).sub (h.const_mul m)
  convert ht using 1
  funext r
  dsimp [entropyDual]
  ring

end BoltzmannNonuniqueness

end

end

section

/-!
# The scalar power singularity in an axial slice

The exponent `r = 1-q` lies between `-1` and `0`. The interval estimate
below is uniform in the location of its singularity. Values at the
single singular point use the real-power convention and are immaterial.
-/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.AxialSlices

theorem intervalIntegrable_abs_rpow {r : ℝ} (hr : -1 < r) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => |x| ^ r) volume a b := by
  have hl : LocallyIntegrable (fun x : ℝ => |x| ^ r) := by
    apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := -r)
      (by simp) (by norm_num only [Module.finrank_self, Nat.cast_one]; linarith)
    · filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      simp only [one_mul, neg_neg, Real.norm_eq_abs, le_refl]
    · exact (measurable_abs.pow measurable_const).aestronglyMeasurable
  exact (intervalIntegrable_iff').mpr (hl.integrableOn_isCompact isCompact_uIcc)

theorem intervalIntegrable_abs_sub_rpow {r : ℝ} (hr : -1 < r) (t a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => |x - t| ^ r) volume a b := by
  simpa using (intervalIntegrable_abs_rpow hr (a - t) (b - t)).comp_sub_right t

theorem integral_abs_rpow_zero {r L : ℝ} (hr : -1 < r) (hL : 0 ≤ L) :
    (∫ x : ℝ in 0..L, |x| ^ r) = L ^ (r + 1) / (r + 1) := by
  rw [intervalIntegral.integral_congr_Ioo_of_le hL (fun x hx => by
    rw [abs_of_pos hx.1])]
  rw [integral_rpow (Or.inl hr), Real.zero_rpow (by linarith : r + 1 ≠ 0), sub_zero]

theorem integral_abs_rpow_symmetric {r L : ℝ} (hr : -1 < r) (hL : 0 ≤ L) :
    (∫ x : ℝ in -L..L, |x| ^ r) = 2 * L ^ (r + 1) / (r + 1) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_abs_rpow hr (-L) 0) (intervalIntegrable_abs_rpow hr 0 L)]
  have hn : (∫ x : ℝ in -L..0, |x| ^ r) = ∫ x : ℝ in 0..L, |x| ^ r := by
    have h := intervalIntegral.integral_comp_neg (fun x : ℝ => |x| ^ r) (a := 0) (b := L)
    simp only [abs_neg, neg_zero] at h
    exact h.symm
  rw [hn, integral_abs_rpow_zero hr hL]
  ring

/-- A power singularity has at most twice the endpoint mass on an interval of length `b-a`.
This is the root-independent estimate in the large-slope case of `ker:scalar-interval`. -/
theorem integral_abs_sub_rpow_le {r a b t : ℝ} (hr : -1 < r) (hr₀ : r ≤ 0)
    (hab : a ≤ b) :
    (∫ x : ℝ in a..b, |x - t| ^ r) ≤ 2 * (b - a) ^ (r + 1) / (r + 1) := by
  have hr₁ : 0 < r + 1 := by linarith
  have hp : 0 ≤ (b - a) ^ (r + 1) / (r + 1) := by positivity
  rw [show 2 * (b - a) ^ (r + 1) / (r + 1) =
    2 * ((b - a) ^ (r + 1) / (r + 1)) by ring]
  by_cases hta : t ≤ a
  · have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hab
      (intervalIntegrable_abs_sub_rpow hr t a b)
      (intervalIntegrable_abs_sub_rpow hr a a b)
      (fun x hx => by
        apply Real.rpow_le_rpow_of_nonpos
        · rw [abs_of_pos (sub_pos.mpr hx.1)]; exact sub_pos.mpr hx.1
        · rw [abs_of_pos (sub_pos.mpr hx.1), abs_of_nonneg (by linarith [hx.1])]
          linarith
        · exact hr₀)
    have he : (∫ x : ℝ in a..b, |x - a| ^ r) =
        (b - a) ^ (r + 1) / (r + 1) := by
      rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => |x| ^ r)]
      simpa using integral_abs_rpow_zero hr (sub_nonneg.mpr hab)
    rw [he] at hmono
    linarith
  by_cases hbt : b ≤ t
  · have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hab
      (intervalIntegrable_abs_sub_rpow hr t a b)
      (intervalIntegrable_abs_sub_rpow hr b a b)
      (fun x hx => by
        apply Real.rpow_le_rpow_of_nonpos
        · rw [abs_of_neg (sub_neg.mpr hx.2)]; linarith [hx.2]
        · rw [abs_of_neg (sub_neg.mpr hx.2), abs_of_nonpos (by linarith [hx.2])]
          linarith
        · exact hr₀)
    have he : (∫ x : ℝ in a..b, |x - b| ^ r) =
        (b - a) ^ (r + 1) / (r + 1) := by
      calc
        _ = ∫ x : ℝ in a..b, |b - x| ^ r := by
          apply intervalIntegral.integral_congr
          intro x _
          exact congrArg (fun y : ℝ => y ^ r) (abs_sub_comm x b)
        _ = _ := by
          rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => |x| ^ r), sub_self]
          exact integral_abs_rpow_zero hr (sub_nonneg.mpr hab)
    rw [he] at hmono
    linarith
  · have hta' : a ≤ t := le_of_not_ge hta
    have htb' : t ≤ b := le_of_not_ge hbt
    have hmono := intervalIntegral.integral_mono_interval
      (show t - (b - a) ≤ a by linarith) hab
      (show b ≤ t + (b - a) by linarith)
      (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (abs_nonneg (x - t)) r))
      (intervalIntegrable_abs_sub_rpow hr t (t - (b - a)) (t + (b - a)))
    calc
      _ ≤ ∫ x : ℝ in t - (b - a)..t + (b - a), |x - t| ^ r := hmono
      _ = 2 * ((b - a) ^ (r + 1) / (r + 1)) := by
        rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => |x| ^ r)]
        rw [show t - (b - a) - t = -(b - a) by ring,
          show t + (b - a) - t = b - a by ring,
          integral_abs_rpow_symmetric hr (sub_nonneg.mpr hab)]
        ring

theorem abs_affine_rpow (r A B x : ℝ) (hB : B ≠ 0) :
    |A - B * x| ^ r = |B| ^ r * |x - A / B| ^ r := by
  have he : A - B * x = -B * (x - A / B) := by field_simp; ring
  rw [he, abs_mul, abs_neg, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]

theorem intervalIntegrable_abs_affine_rpow {r : ℝ} (hr : -1 < r) (A B a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => |A - B * x| ^ r) volume a b := by
  by_cases hB : B = 0
  · simp only [hB, zero_mul, sub_zero]
    exact intervalIntegrable_const
  · have hi := (intervalIntegrable_abs_sub_rpow hr (A / B) a b).const_mul (|B| ^ r)
    convert hi using 1
    funext x
    exact abs_affine_rpow r A B x hB

/-- Large-slope estimate obtained by rescaling the root-independent interval bound. -/
theorem integral_abs_affine_rpow_le {r a b A B : ℝ} (hr : -1 < r) (hr₀ : r ≤ 0)
    (hab : a ≤ b) (hB : B ≠ 0) :
    (∫ x : ℝ in a..b, |A - B * x| ^ r) ≤
      |B| ^ r * (2 * (b - a) ^ (r + 1) / (r + 1)) := by
  simp_rw [abs_affine_rpow r A B _ hB]
  rw [intervalIntegral.integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_abs_sub_rpow_le hr hr₀ hab)
    (Real.rpow_nonneg (abs_nonneg B) r)

/-- If the slope is small, the affine function stays a fixed distance from zero. -/
theorem small_slope_distance {A B R x : ℝ} (_hR : 0 ≤ R)
    (hAB : 2 * R * |B| ≤ |A|) (hx : |x| ≤ R) :
    |A| / 2 ≤ |A - B * x| := by
  have hmul : |B * x| ≤ |B| * R := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg B)
  have htri := abs_add_le (A - B * x) (B * x)
  rw [sub_add_cancel] at htri
  nlinarith

/-- The small-slope half of the scalar estimate, before combining the powers of the length. -/
theorem integral_abs_affine_rpow_le_small_slope {r a b A B R : ℝ}
    (hr : -1 < r) (hr₀ : r ≤ 0) (hab : a ≤ b)
    (hR : 0 ≤ R) (ha : -R ≤ a) (hb : b ≤ R) (hA : A ≠ 0)
    (hAB : 2 * R * |B| ≤ |A|) :
    (∫ x : ℝ in a..b, |A - B * x| ^ r) ≤ (b - a) * (|A| / 2) ^ r := by
  have h := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_abs_affine_rpow hr A B a b)
    (intervalIntegrable_const (c := (|A| / 2) ^ r))
    (fun x hx => Real.rpow_le_rpow_of_nonpos (by positivity : 0 < |A| / 2)
      (small_slope_distance hR hAB (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩)) hr₀)
  simpa using h

def scalarConstant (r : ℝ) : ℝ := (2 : ℝ) ^ (-r) * ((2 : ℝ) ^ (-r) + 2 / (r + 1))

theorem scalarConstant_pos {r : ℝ} (hr : -1 < r) : 0 < scalarConstant r := by
  have hr₁ : 0 < r + 1 := by linarith
  unfold scalarConstant
  positivity

private theorem length_le_scaled_power {r l R : ℝ} (hr : r ≤ 0)
    (hl : 0 < l) (hlR : l ≤ 2 * R) :
    l ≤ (2 * R) ^ (-r) * l ^ (r + 1) := by
  have hp := Real.rpow_le_rpow hl.le hlR (neg_nonneg.mpr hr)
  calc
    l = l ^ (r + 1) * l ^ (-r) := by
      rw [← Real.rpow_add hl, show (r + 1) + -r = 1 by ring, Real.rpow_one]
    _ ≤ l ^ (r + 1) * (2 * R) ^ (-r) :=
      mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hl.le _)
    _ = _ := mul_comm _ _

/-- The scalar interval estimate `ker:scalar-interval`, with an explicit constant.
The singular case `A=0` is understood in the extended sense in the manuscript;
the finite estimate needed off the exceptional line is stated here. -/
theorem integral_abs_affine_rpow_scalar_bound {r a b A B R : ℝ}
    (hr : -1 < r) (hr₀ : r ≤ 0) (hab : a < b) (hR : 0 < R)
    (ha : -R ≤ a) (hb : b ≤ R) (hA : A ≠ 0) :
    (∫ x : ℝ in a..b, |A - B * x| ^ r) ≤
      scalarConstant r * (R ^ (-r) * (b - a) ^ (r + 1) * |A| ^ r) := by
  have hr₁ : 0 < r + 1 := by linarith
  have hA₀ : 0 < |A| := abs_pos.mpr hA
  have hl : 0 < b - a := sub_pos.mpr hab
  have hlR : b - a ≤ 2 * R := by linarith
  have hn : 0 ≤ R ^ (-r) * (b - a) ^ (r + 1) * |A| ^ r := by positivity
  have htwo : 0 ≤ (2 : ℝ) ^ (-r) := Real.rpow_nonneg (by norm_num) _
  have hc₁ : (2 : ℝ) ^ (-r) * (2 : ℝ) ^ (-r) ≤ scalarConstant r := by
    unfold scalarConstant
    have hdiv : 0 ≤ 2 / (r + 1) := by positivity
    nlinarith
  have hc₂ : (2 : ℝ) ^ (-r) * (2 / (r + 1)) ≤ scalarConstant r := by
    unfold scalarConstant
    nlinarith
  by_cases hsmall : 2 * R * |B| ≤ |A|
  · calc
      _ ≤ (b - a) * (|A| / 2) ^ r :=
        integral_abs_affine_rpow_le_small_slope hr hr₀ hab.le hR.le ha hb hA hsmall
      _ ≤ ((2 * R) ^ (-r) * (b - a) ^ (r + 1)) * (|A| / 2) ^ r :=
        mul_le_mul_of_nonneg_right (length_le_scaled_power hr₀ hl hlR)
          (Real.rpow_nonneg (by positivity) _)
      _ = ((2 : ℝ) ^ (-r) * (2 : ℝ) ^ (-r)) *
          (R ^ (-r) * (b - a) ^ (r + 1) * |A| ^ r) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hR.le,
          Real.div_rpow hA₀.le (by norm_num : (0 : ℝ) ≤ 2),
          div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc₁ hn
  · have hlarge : |A| < 2 * R * |B| := lt_of_not_ge hsmall
    have hB : B ≠ 0 := by
      intro hzero
      simp only [hzero, abs_zero, mul_zero] at hlarge
      linarith
    have hdiv : |A| / (2 * R) ≤ |B| :=
      ((div_lt_iff₀ (by positivity : 0 < 2 * R)).mpr (by nlinarith)).le
    have hp := Real.rpow_le_rpow_of_nonpos
      (by positivity : 0 < |A| / (2 * R)) hdiv hr₀
    calc
      _ ≤ |B| ^ r * (2 * (b - a) ^ (r + 1) / (r + 1)) :=
        integral_abs_affine_rpow_le hr hr₀ hab.le hB
      _ ≤ (|A| / (2 * R)) ^ r * (2 * (b - a) ^ (r + 1) / (r + 1)) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
      _ = ((2 : ℝ) ^ (-r) * (2 / (r + 1))) *
          (R ^ (-r) * (b - a) ^ (r + 1) * |A| ^ r) := by
        rw [Real.div_rpow hA₀.le (by positivity : 0 ≤ 2 * R),
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hR.le]
        rw [div_eq_mul_inv, mul_inv_rev,
          ← Real.rpow_neg hR.le, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc₂ hn

/-- The manuscript's scalar slice estimate in its `q` notation. -/
theorem scalar_interval_bound {q a b A B R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hab : a < b) (hR : 0 < R)
    (ha : -R ≤ a) (hb : b ≤ R) (hA : A ≠ 0) :
    (∫ x : ℝ in a..b, |A - B * x| ^ (1 - q)) ≤
      scalarConstant (1 - q) * (R ^ (q - 1) * (b - a) ^ (2 - q) * |A| ^ (1 - q)) := by
  have h := integral_abs_affine_rpow_scalar_bound (r := 1 - q) (B := B)
    (by linarith) (by linarith) hab hR ha hb hA
  simpa only [show -(1 - q) = q - 1 by ring, show (1 - q) + 1 = 2 - q by ring] using h

end BoltzmannNonuniqueness.AxialSlices

end

end

section

/-! # Convex bounds for entropy under truncation and addition -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness

theorem scalarRelativeEntropy_convex (m : ℝ) :
    ConvexOn ℝ (Ici (0:ℝ)) (scalarRelativeEntropy m) := by
  refine ⟨convex_Ici _,?_⟩
  intro x hx y hy a b ha hb hab
  have h := Real.convexOn_mul_log.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h ⊢
  unfold scalarRelativeEntropy
  calc
    _ = (a*x+b*y)*Real.log (a*x+b*y)-(a*x+b*y)*(1+Real.log m)+(a+b)*m := by rw [hab]; ring
    _ ≤ (a*(x*Real.log x)+b*(y*Real.log y))-(a*x+b*y)*(1+Real.log m)+(a+b)*m := by linarith
    _ = _ := by ring

theorem scalarRelativeEntropy_double (m x : ℝ) :
    scalarRelativeEntropy m (2*x) = 2*scalarRelativeEntropy m x+2*x*Real.log 2-m := by
  by_cases hx : x = 0
  · simp only [hx,scalarRelativeEntropy,mul_zero,zero_mul,sub_zero]
    ring
  · rw [scalarRelativeEntropy,Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hx]
    unfold scalarRelativeEntropy
    ring

theorem scalarRelativeEntropy_add_le {m a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    scalarRelativeEntropy m (a+b) ≤ scalarRelativeEntropy m a+scalarRelativeEntropy m b+
      (a+b)*Real.log 2-m := by
  have h := (scalarRelativeEntropy_convex m).2 (show 2*a ∈ Ici (0:ℝ) by change 0 ≤ 2*a; positivity)
    (show 2*b ∈ Ici (0:ℝ) by change 0 ≤ 2*b; positivity)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ)+1/2 = 1)
  simp only [smul_eq_mul] at h
  rw [show (1/2:ℝ)*(2*a)+(1/2)*(2*b) = a+b by ring,
    scalarRelativeEntropy_double,scalarRelativeEntropy_double] at h
  linarith

theorem scalarRelativeEntropy_le_of_le {m u v : ℝ} (hm : 0 < m) (hu : 0 ≤ u) (huv : u ≤ v) :
    scalarRelativeEntropy m u ≤ scalarRelativeEntropy m v+m := by
  have hv : 0 ≤ scalarRelativeEntropy m v := by
    rw [scalarRelativeEntropy_eq hm]
    exact relativeEntropyDensity_nonneg (hu.trans huv) hm
  have h := (scalarRelativeEntropy_convex m).le_max_of_mem_Icc
    (show (0:ℝ) ∈ Ici (0:ℝ) by simp) (show v ∈ Ici (0:ℝ) by exact hu.trans huv) ⟨hu,huv⟩
  have hz : scalarRelativeEntropy m 0 = m := by simp [scalarRelativeEntropy]
  rw [hz] at h
  exact h.trans (max_le (by linarith) (by linarith [hm.le]))

end BoltzmannNonuniqueness

end

end

end OAI
