import Mathlib
import OAI.Analysis.CoulombIonization.Variational.BindingBase

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

lemma SmoothMultiplier.weighted_kinetic_nonneg (P : E →L[ℝ] Space) (v : Fin 3 → E)
    (hPv : ∀ a, P (v a) = EuclideanSpace.single a 1) (p : SmoothMultiplier v)
    (hp : ∀ x, (∑ a : Fin 3, (lineDeriv ℝ p.value x (v a)) ^ 2) ≤
      (p.value x) ^ 2 / (4 * ‖P x‖ ^ 2)) (F : weakGraph v) :
    0 ≤ ∑ a : Fin 3, (⟪(p.apply (p.apply F)).val (some a), F.val (some a)⟫_ℂ).re := by
  have hh := linear_hardy_bound P v hPv (Lp.memLp ((p.apply F).val none))
    (fun a => Lp.memLp ((p.apply F).val (some a)))
    ((mem_weakGraph v (p.apply F).val).mp (p.apply F).property)
  have hi (a : Fin 3) : Integrable (fun x =>
      (lineDeriv ℝ p.value x (v a)) ^ 2 * ‖F.val none x‖ ^ 2) := by
    obtain ⟨C,hC⟩ := p.gradient_bound a
    apply (Lp.memLp (F.val none)).norm.integrable_sq.bdd_mul (c := C ^ 2)
      ((p.derivative_continuous a).pow 2).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      change ‖lineDeriv ℝ p.value x (v a) ^ 2‖ ≤ C ^ 2
      rw [norm_pow, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hC x) 2
  have hims (a : Fin 3) : ‖(p.apply F).val (some a)‖ ^ 2 -
      (⟪(p.apply (p.apply F)).val (some a), F.val (some a)⟫_ℂ).re =
        ∫ x, (lineDeriv ℝ p.value x (v a)) ^ 2 * ‖F.val none x‖ ^ 2 := by
    apply l2_ims_identity p.value (fun x => lineDeriv ℝ p.value x (v a))
      (F.val (some a)) (F.val none) ((p.apply F).val (some a))
      ((p.apply (p.apply F)).val (some a)) (p.apply_gradient F a)
    filter_upwards [p.apply_gradient (p.apply F) a, p.apply_value F] with x hx hy
    rw [hx, hy]
  have hl : (∑ a : Fin 3, ∫ x, (lineDeriv ℝ p.value x (v a)) ^ 2 * ‖F.val none x‖ ^ 2) ≤
      ∫ x, ‖(p.apply F).val none x‖ ^ 2 / (4 * ‖P x‖ ^ 2) := by
    rw [← integral_finsetSum _ fun a _ => hi a]
    apply integral_mono_ae (integrable_finsetSum _ fun a _ => hi a) hh.1
    filter_upwards [p.apply_value F] with x hx
    rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
      ← Finset.sum_mul]
    have h := mul_le_mul_of_nonneg_right (hp x) (sq_nonneg ‖F.val none x‖)
    convert h using 1
    ring
  have hsum := hl.trans hh.2
  simp_rw [← hims, ← l2_norm_sq] at hsum
  rw [Finset.sum_sub_distrib] at hsum
  linarith

end

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

def bindingWeight (R ε : ℝ) (x : Space) : ℝ :=
  R * regularizedRadius ε x / (R + regularizedRadius ε x)

def bindingRoot (R ε : ℝ) (x : Space) : ℝ := Real.sqrt (bindingWeight R ε x)

lemma bindingWeight_pos {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (x : Space) :
    0 < bindingWeight R ε x := by
  unfold bindingWeight
  have ht := regularizedRadius_pos hε x
  positivity

lemma bindingWeight_le {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (x : Space) :
    bindingWeight R ε x ≤ R := by
  have ht := regularizedRadius_pos hε x
  unfold bindingWeight
  apply (div_le_iff₀ (by positivity : 0 < R + regularizedRadius ε x)).mpr
  nlinarith [sq_nonneg R]

lemma bindingWeight_le_radius {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (x : Space) :
    bindingWeight R ε x ≤ regularizedRadius ε x := by
  have ht := regularizedRadius_pos hε x
  unfold bindingWeight
  apply (div_le_iff₀ (by positivity : 0 < R + regularizedRadius ε x)).mpr
  nlinarith [sq_nonneg (regularizedRadius ε x)]

lemma bindingRoot_sq {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (x : Space) :
    bindingRoot R ε x ^ 2 = bindingWeight R ε x :=
  Real.sq_sqrt (bindingWeight_pos hR hε x).le

lemma bindingRoot_pos {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (x : Space) :
    0 < bindingRoot R ε x := Real.sqrt_pos.mpr (bindingWeight_pos hR hε x)

lemma bindingRoot_bound {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (x : Space) :
    |bindingRoot R ε x| ≤ Real.sqrt R := by
  rw [abs_of_pos (bindingRoot_pos hR hε x)]
  exact Real.sqrt_le_sqrt (bindingWeight_le hR hε x)

lemma bindingRoot_smooth {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ContDiff ℝ ∞ (bindingRoot R ε) := by
  apply ContDiff.sqrt
  · apply ContDiff.div
    · exact contDiff_const.mul (regularizedRadius_smooth hε)
    · exact contDiff_const.add (regularizedRadius_smooth hε)
    · intro x; have ht := regularizedRadius_pos hε x; positivity
  · intro x; exact (bindingWeight_pos hR hε x).ne'

lemma bindingRoot_derivative {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (a : Fin 3) (x : Space) :
    fderiv ℝ (bindingRoot R ε) x (EuclideanSpace.single a 1) =
      bindingRoot R ε x * R * x a /
        (2 * (regularizedRadius ε x) ^ 2 * (R + regularizedRadius ε x)) := by
  let t := regularizedRadius ε x
  have ht : 0 < t := regularizedRadius_pos hε x
  have hD := ((hasFDerivAt_id (𝕜 := ℝ) x).norm_sq).add_const (ε ^ 2)
  have htD := (Real.hasDerivAt_sqrt (by positivity : ‖x‖ ^ 2 + ε ^ 2 ≠ 0)).comp_hasFDerivAt x hD
  have hw := ((hasDerivAt_id t).const_mul R).div
    ((hasDerivAt_id t).const_add R) (by positivity : R + t ≠ 0)
  have hs := (Real.hasDerivAt_sqrt (by positivity : R * t / (R+t) ≠ 0)).comp t hw
  have hh := hs.comp_hasFDerivAt x htD
  change HasFDerivAt (bindingRoot R ε) _ x at hh
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    innerSL_apply_apply, EuclideanSpace.inner_single_right, conj_trivial, one_mul]
  have hp := bindingRoot_pos hR hε x
  have he := bindingRoot_sq hR hε x
  change bindingRoot R ε x ^ 2 = R*t/(R+t) at he
  simp only [smul_eq_mul, nsmul_eq_mul, id_eq, mul_one]
  change (1 / (2 * bindingRoot R ε x)) *
    ((R * (R+t) - R*t) / (R+t)^2) *
    ((1 / (2 * t)) * (2 * x a)) =
      bindingRoot R ε x * R * x a / (2 * t^2 * (R+t))
  have he' : bindingRoot R ε x ^ 2 * (R+t) = R*t := (eq_div_iff (by positivity)).mp he
  field_simp
  rw [he']
  ring

lemma bindingRoot_gradient_bound {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (a : Fin 3) (x : Space) :
    |fderiv ℝ (bindingRoot R ε) x (EuclideanSpace.single a 1)| ≤
      Real.sqrt R / (2 * ε) := by
  let t := regularizedRadius ε x
  have ht : 0 < t := regularizedRadius_pos hε x
  have hp := bindingRoot_pos hR hε x
  have hx : |x a| ≤ t := by
    have hc := radialField_norm_le hε a x
    change ‖x a / t‖ ≤ 1 at hc
    rw [norm_div, Real.norm_eq_abs, Real.norm_of_nonneg ht.le, div_le_one ht] at hc
    exact hc
  rw [bindingRoot_derivative hR hε, abs_div, abs_mul, abs_mul,
    abs_of_pos hp, abs_of_pos hR, abs_of_pos (by positivity : 0 < 2 * t^2 * (R+t))]
  change bindingRoot R ε x * R * |x a| / (2*t^2*(R+t)) ≤ _
  calc
    _ ≤ Real.sqrt R * R * t / (2*t^2*(R+t)) := by
      gcongr
      exact (abs_of_pos hp ▸ bindingRoot_bound hR hε x)
    _ ≤ Real.sqrt R / (2*t) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_nonneg (Real.sqrt_nonneg R) (pow_nonneg ht.le 3)]
    _ ≤ _ := div_le_div_of_nonneg_left (Real.sqrt_nonneg R) (by positivity)
      (by gcongr; exact le_regularizedRadius hε.le x)

lemma bindingRoot_hardy_control {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (x : Space) :
    (∑ a : Fin 3, (fderiv ℝ (bindingRoot R ε) x (EuclideanSpace.single a 1)) ^ 2) ≤
      bindingRoot R ε x ^ 2 / (4 * ‖x‖ ^ 2) := by
  simp only [bindingRoot_derivative hR hε, div_pow, mul_pow,
    ← Finset.sum_div, ← Finset.mul_sum, sum_coordinate_sq]
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let t := regularizedRadius ε x
  have ht : 0 < t := regularizedRadius_pos hε x
  have hnt : ‖x‖ ≤ t := norm_le_regularizedRadius ε x
  change bindingRoot R ε x ^ 2 * R^2 * ‖x‖^2 /
    (2^2 * (t^2)^2 * (R+t)^2) ≤ _
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hfour : ‖x‖^4 ≤ t^4 := pow_le_pow_left₀ (norm_nonneg _) hnt 4
  have hRs : R^2 ≤ (R+t)^2 := by nlinarith
  have hm := mul_le_mul hfour hRs (sq_nonneg R) (pow_nonneg ht.le 4)
  have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 4 * bindingRoot R ε x ^ 2 by positivity)
  nlinarith [sq_nonneg (bindingRoot R ε x)]


open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace

end CoulombAtom

end

end OAI
