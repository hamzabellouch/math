import Mathlib
import OAI.Combinatorics.StripMass.CauchyMatrices

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
theorem quartic_weighted_integral_sqrt {r : ℝ} (hr : 0 < r) :
    (∫ t in Ioi 0, quarticWeighted r t) = Real.pi * Real.sqrt ((1 + r) / 2) := by
  rw [(quartic_weighted_integral hr).2]
  have hs : Real.sqrt (2 + 2 * r) = 2 * Real.sqrt ((1 + r) / 2) := by
    rw [show 2 + 2 * r = 4 * ((1 + r) / 2) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [hs]
  apply (div_eq_iff (by positivity : 2 * Real.sqrt ((1 + r) / 2) ≠ 0)).2
  have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (1 + r) / 2)
  linear_combination -2 * Real.pi * hsq

def minusBranch (s : ℝ) : ℝ := Real.sqrt ((1 + Real.sqrt ((1 + s) / 2)) / 2)

theorem minusBranch_zero : minusBranch 0 = Real.cos (Real.pi / 8) := by
  rw [Real.cos_pi_div_eight]
  have h : Real.sqrt ((1 + (0 : ℝ)) / 2) = Real.sqrt 2 / 2 := by
    have ha := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (1 + 0) / 2)
    have hb := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hna := Real.sqrt_nonneg ((1 + (0 : ℝ)) / 2)
    have hnb := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  unfold minusBranch
  rw [h]
  have ha := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (1 + Real.sqrt 2 / 2) / 2)
  have hb := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + Real.sqrt 2)
  have hna := Real.sqrt_nonneg ((1 + Real.sqrt 2 / 2) / 2)
  have hnb := Real.sqrt_nonneg (2 + Real.sqrt 2)
  nlinarith

theorem transformed_omega {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    |(-8 * t * (t ^ 2 + 1) / uniformDen t ^ 2)| •
        (s * omega (uniformizer t) / (1 + s * uniformizer t)) =
      quarticWeighted (Real.sqrt ((1 + s) / 2)) t -
        quarticWeighted (Real.sqrt (1 / 2)) t := by
  rw [omega_uniformizer ht, abs_of_neg (by
    exact div_neg_of_neg_of_pos (by nlinarith [sq_nonneg t])
      (sq_pos_of_pos (uniformDen_pos t))), smul_eq_mul]
  unfold quarticWeighted quarticDen
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (1 + s) / 2),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  unfold uniformizer uniformDen
  field_simp
  ring

theorem omega_resolvent {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun x => s * omega x / (1 + s * x)) (Ioo 0 1) ∧
      (∫ x in Ioo 0 1, s * omega x / (1 + s * x)) =
        Real.pi * (minusBranch s - minusBranch 0) := by
  have hr : 0 < Real.sqrt ((1 + s) / 2) := by positivity
  have hr0 : 0 < Real.sqrt ((1 : ℝ) / 2) := by positivity
  have hint := (quartic_weighted_integral hr).1.sub (quartic_weighted_integral hr0).1
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun t _ => (uniformizer_deriv t).hasDerivWithinAt) uniformizer_inj
    (fun x => s * omega x / (1 + s * x))
  rw [uniformizer_image] at hi
  constructor
  · apply hi.2
    exact IntegrableOn.congr_fun hint (fun t ht => (transformed_omega hs ht).symm)
      measurableSet_Ioi
  · have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun t _ => (uniformizer_deriv t).hasDerivWithinAt) uniformizer_inj
      (fun x => s * omega x / (1 + s * x))
    rw [uniformizer_image] at h
    rw [h, setIntegral_congr_fun measurableSet_Ioi (fun t ht => transformed_omega hs ht),
      integral_sub (quartic_weighted_integral hr).1 (quartic_weighted_integral hr0).1,
      quartic_weighted_integral_sqrt hr, quartic_weighted_integral_sqrt hr0]
    simp only [minusBranch, add_zero]
    ring

 

theorem stieltjes_omega {z : ℝ} (hz : z < 0) :
    Real.sqrt ((1 + Real.sqrt ((1 - 1 / z) / 2)) / 2) =
      Real.cos (Real.pi / 8) + (1 / Real.pi) *
        ∫ x in Ioo (0 : ℝ) 1, omega x / (x - z) := by
  have hs : 0 < -1 / z := div_pos_of_neg_of_neg (by norm_num) hz
  have heq : EqOn (fun x => (-1 / z) * omega x / (1 + (-1 / z) * x))
      (fun x => omega x / (x - z)) (Ioo 0 1) := by
    intro x hx
    dsimp only
    have ha : 1 + (-1 / z) * x ≠ 0 := ne_of_gt (by have := hx.1; positivity)
    have hb : x - z ≠ 0 := by linarith [hx.1]
    apply (div_eq_div_iff ha hb).2
    field_simp [hz.ne]
    ring
  have h := (omega_resolvent hs).2
  rw [setIntegral_congr_fun measurableSet_Ioo heq, minusBranch_zero] at h
  have he : minusBranch (-1 / z) =
      Real.sqrt ((1 + Real.sqrt ((1 - 1 / z) / 2)) / 2) := by
    unfold minusBranch
    congr 4
    ring
  rw [he] at h
  rw [h]
  field_simp
  ring

def lBranch (x : ℝ) : ℝ := Real.sqrt (1 + Real.sqrt ((1 + 1 / x) / 2))

theorem stieltjes_lBranch {z : ℝ} (hz : 0 < z) :
    lBranch z = Real.sqrt 2 * Real.cos (Real.pi / 8) +
      (Real.sqrt 2 / Real.pi) * ∫ x in Ioo (0 : ℝ) 1, omega x / (x + z) := by
  have h := stieltjes_omega (neg_neg_of_pos hz)
  have heq : lBranch z = Real.sqrt 2 *
      Real.sqrt ((1 + Real.sqrt ((1 - 1 / (-z)) / 2)) / 2) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    unfold lBranch
    congr 2
    field_simp
    ring_nf
  rw [heq, h]
  simp only [sub_neg_eq_add]
  ring

def squareWeight (x : ℝ) : ℝ := Real.sqrt ((1 - x) / (8 * x))

theorem lBranch_mul_omega {x : ℝ} (hx : x ∈ Ioo 0 1) :
    lBranch x * omega x = squareWeight x := by
  have hx0 : 0 < x := hx.1
  have heq : (1 + 1 / x) / 2 = (1 + x) / (2 * x) := by
    field_simp [hx0.ne']
    ring
  have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (1 + x) / (2 * x))
  have hp : (1 + Real.sqrt ((1 + x) / (2 * x))) *
      (Real.sqrt ((1 + x) / (2 * x)) - 1) = (1 - x) / (2 * x) := by
    calc
      _ = (1 + x) / (2 * x) - 1 := by nlinarith
      _ = _ := by field_simp [hx0.ne']; ring
  unfold lBranch omega squareWeight
  rw [heq, ← mul_assoc, mul_comm (Real.sqrt _) (1 / 2 : ℝ), mul_assoc,
    ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 1 + Real.sqrt ((1 + x) / (2 * x))), hp]
  have heq2 : (1 - x) / (8 * x) = (1 / 4) * ((1 - x) / (2 * x)) := by ring
  rw [heq2, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  norm_num

theorem scaled_cauchy_Ioi {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), (a ^ 2 + t ^ 2)⁻¹) = Real.pi / (2 * a) := by
  have heq : (fun t : ℝ => (a ^ 2 + t ^ 2)⁻¹) =
      fun t => (a ^ 2)⁻¹ * (1 + (a⁻¹ * t) ^ 2)⁻¹ := by
    funext t
    field_simp
  rw [heq, integral_const_mul, integral_comp_mul_left_Ioi (fun t : ℝ => (1 + t ^ 2)⁻¹) 0 (inv_pos.2 ha)]
  simp only [mul_zero, inv_inv, smul_eq_mul, integral_Ioi_inv_one_add_sq,
    Real.arctan_zero, sub_zero]
  field_simp

def squareUniformizer (t : ℝ) : ℝ := 1 / (1 + t ^ 2)

theorem squareUniformizer_deriv (t : ℝ) :
    HasDerivAt squareUniformizer (-2 * t / (1 + t ^ 2) ^ 2) t := by
  have hd : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
    simpa using ((hasDerivAt_id t).pow 2).const_add 1
  change HasDerivAt (fun t : ℝ => 1 / (1 + t ^ 2)) _ t
  exact (((hasDerivAt_const t (1 : ℝ)).div hd
    (show 1 + t ^ 2 ≠ 0 by positivity))).congr_deriv (by ring)

theorem squareUniformizer_inj : InjOn squareUniformizer (Ioi 0) := by
  apply StrictAntiOn.injOn
  intro x hx y hy hxy
  unfold squareUniformizer
  apply one_div_lt_one_div_of_lt (by positivity)
  gcongr
  exact le_of_lt hx

theorem squareUniformizer_image : squareUniformizer '' Ioi 0 = Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨by unfold squareUniformizer; positivity, ?_⟩
    unfold squareUniformizer
    rw [div_lt_one (by positivity)]
    exact lt_add_of_pos_right 1 (sq_pos_of_pos ht)
  · intro hx
    have hpos : 0 < 1 / x - 1 := by
      rw [sub_pos, one_lt_div hx.1]
      exact hx.2
    have hs := Real.sq_sqrt hpos.le
    refine ⟨Real.sqrt (1 / x - 1), Real.sqrt_pos.2 hpos, ?_⟩
    unfold squareUniformizer
    rw [hs]
    field_simp [hx.1.ne']
    ring

theorem squareWeight_uniformizer {t : ℝ} (ht : 0 < t) :
    squareWeight (squareUniformizer t) = t / (2 * Real.sqrt 2) := by
  have heq : (1 - squareUniformizer t) / (8 * squareUniformizer t) = t ^ 2 / 8 := by
    unfold squareUniformizer
    field_simp
    ring
  unfold squareWeight
  rw [heq, Real.sqrt_div (sq_nonneg t), Real.sqrt_sq ht.le]
  congr 1
  rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

theorem transformed_squareWeight {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    |(-2 * t / (1 + t ^ 2) ^ 2)| •
        (s * squareWeight (squareUniformizer t) / (1 + s * squareUniformizer t)) =
      (1 / Real.sqrt 2) * ((1 + s) * ((1 + s) + t ^ 2)⁻¹ - (1 + t ^ 2)⁻¹) := by
  rw [squareWeight_uniformizer ht, abs_of_neg (by
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)), smul_eq_mul]
  unfold squareUniformizer
  field_simp
  ring

theorem squareWeight_resolvent {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun x => s * squareWeight x / (1 + s * x)) (Ioo 0 1) ∧
      (∫ x in Ioo 0 1, s * squareWeight x / (1 + s * x)) =
        (Real.pi / (2 * Real.sqrt 2)) * (Real.sqrt (1 + s) - 1) := by
  let a := Real.sqrt (1 + s)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha2 : a ^ 2 = 1 + s := Real.sq_sqrt (by positivity)
  have hint1 : IntegrableOn (fun t : ℝ => ((1 + s) + t ^ 2)⁻¹) (Ioi 0) := by
    rw [← ha2]
    exact (scaled_cauchy ha).1.integrableOn
  have hint0 : IntegrableOn (fun t : ℝ => (1 + t ^ 2)⁻¹) (Ioi 0) :=
    integrable_inv_one_add_sq.integrableOn
  have hint := ((hint1.const_mul (1 + s)).sub hint0).const_mul (1 / Real.sqrt 2)
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun t _ => (squareUniformizer_deriv t).hasDerivWithinAt) squareUniformizer_inj
    (fun x => s * squareWeight x / (1 + s * x))
  rw [squareUniformizer_image] at hi
  constructor
  · apply hi.2
    exact IntegrableOn.congr_fun hint (fun t ht => (transformed_squareWeight hs ht).symm)
      measurableSet_Ioi
  · have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun t _ => (squareUniformizer_deriv t).hasDerivWithinAt) squareUniformizer_inj
      (fun x => s * squareWeight x / (1 + s * x))
    rw [squareUniformizer_image] at h
    rw [h, setIntegral_congr_fun measurableSet_Ioi (fun t ht => transformed_squareWeight hs ht),
      integral_const_mul, integral_sub (hint1.const_mul (1 + s)) hint0,
      integral_const_mul, ← ha2, scaled_cauchy_Ioi ha, integral_Ioi_inv_one_add_sq,
      Real.arctan_zero, sub_zero]
    rw [Real.sqrt_sq ha.le]
    field_simp

theorem stieltjes_omega_square {z : ℝ} (hz : z < 0) :
    (Real.sqrt ((1 + Real.sqrt ((1 - 1 / z) / 2)) / 2)) ^ 2 =
      (Real.cos (Real.pi / 8)) ^ 2 + (1 / Real.pi) *
        ∫ x in Ioo (0 : ℝ) 1, lBranch x * omega x / (x - z) := by
  have hs : 0 < -1 / z := div_pos_of_neg_of_neg (by norm_num) hz
  have heq : EqOn (fun x => (-1 / z) * squareWeight x / (1 + (-1 / z) * x))
      (fun x => lBranch x * omega x / (x - z)) (Ioo 0 1) := by
    intro x hx
    dsimp only
    rw [lBranch_mul_omega hx]
    have ha : 1 + (-1 / z) * x ≠ 0 := ne_of_gt (by have := hx.1; positivity)
    have hb : x - z ≠ 0 := by linarith [hx.1]
    apply (div_eq_div_iff ha hb).2
    field_simp [hz.ne]
    ring
  have h := (squareWeight_resolvent hs).2
  rw [setIntegral_congr_fun measurableSet_Ioo heq] at h
  have hC : (Real.cos (Real.pi / 8)) ^ 2 = (1 + Real.sqrt (1 / 2)) / 2 := by
    rw [← minusBranch_zero]
    unfold minusBranch
    simp only [add_zero]
    exact Real.sq_sqrt (by positivity)
  rw [h, hC, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (1 + Real.sqrt ((1 - 1 / z) / 2)) / 2)]
  have heq' : 1 - 1 / z = 1 + -1 / z := by ring
  rw [heq', Real.sqrt_div (by linarith : (0 : ℝ) ≤ 1 + -1 / z),
    Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
  field_simp
  ring

 

theorem integrableOn_lBranch_omega :
    IntegrableOn (fun x => lBranch x * omega x) (Ioo (0 : ℝ) 1) := by
  have hint := ((squareWeight_resolvent (by norm_num : (0 : ℝ) < 1)).1).const_mul 2
  apply hint.mono'
  · apply Measurable.aestronglyMeasurable
    unfold lBranch omega
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, lBranch_mul_omega hx, abs_of_nonneg (show 0 ≤ squareWeight x from Real.sqrt_nonneg _)]
    simp only [one_mul]
    have hd : 0 < 1 + x := by linarith [hx.1]
    have hw : 0 ≤ squareWeight x := Real.sqrt_nonneg _
    rw [← mul_div_assoc, le_div_iff₀ hd]
    nlinarith [hx.2]


 


theorem integrableOn_continuous_mul {w g : ℝ → ℝ}
    (hw : IntegrableOn w (Ioo (0 : ℝ) 1)) (hg : ContinuousOn g (Icc 0 1)) :
    IntegrableOn (fun x => g x * w x) (Ioo (0 : ℝ) 1) := by
  have hc : IntegrableOn w (Icc (0 : ℝ) 1) := (integrableOn_Icc_iff_integrableOn_Ioo (f := w) (μ := volume)).2 hw
  have h := (hc.mul_continuousOn hg isCompact_Icc).mono_set Ioo_subset_Icc_self
  simpa only [mul_comm] using h

 
def realStieltjes (a : ℝ) (w : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ x in Ioo (0 : ℝ) 1, w x / (z - a * x)

def offCut (a z : ℝ) : Prop := ∀ x ∈ Icc (0 : ℝ) 1, z - a * x ≠ 0

theorem integrableOn_stieltjes {a z : ℝ} {w : ℝ → ℝ}
    (hw : IntegrableOn w (Ioo (0 : ℝ) 1)) (hz : offCut a z) :
    IntegrableOn (fun x => w x / (z - a * x)) (Ioo (0 : ℝ) 1) := by
  have hc : ContinuousOn (fun x : ℝ => (z - a * x)⁻¹) (Icc 0 1) :=
    (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn.inv₀ hz
  simpa only [div_eq_mul_inv, mul_comm] using integrableOn_continuous_mul hw hc

theorem integrableOn_polynomial_weight {a : ℝ} {w : ℝ → ℝ}
    (hw : IntegrableOn w (Ioo (0 : ℝ) 1)) (p : Polynomial ℝ) :
    IntegrableOn (fun x => p.eval (a * x) * w x) (Ioo (0 : ℝ) 1) :=
  integrableOn_continuous_mul hw (p.continuous.comp (continuous_const.mul continuous_id)).continuousOn

theorem realStieltjes_const_mul (a z c : ℝ) (w : ℝ → ℝ) :
    realStieltjes a (fun x => c * w x) z = c * realStieltjes a w z := by
  unfold realStieltjes
  simp only [mul_div_assoc, integral_const_mul]

theorem realStieltjes_add {a z : ℝ} {w v : ℝ → ℝ}
    (hw : IntegrableOn w (Ioo (0 : ℝ) 1)) (hv : IntegrableOn v (Ioo (0 : ℝ) 1))
    (hz : offCut a z) :
    realStieltjes a (fun x => w x + v x) z = realStieltjes a w z + realStieltjes a v z := by
  unfold realStieltjes
  simp only [add_div]
  exact integral_add (integrableOn_stieltjes hw hz) (integrableOn_stieltjes hv hz)

theorem realStieltjes_mul_variable {a z : ℝ} {w : ℝ → ℝ}
    (hw : IntegrableOn w (Ioo (0 : ℝ) 1)) (hz : offCut a z) :
    z * realStieltjes a w z = realStieltjes a (fun x => a * x * w x) z +
      ∫ x in Ioo (0 : ℝ) 1, w x := by
  have hi : IntegrableOn (fun x => a * x * w x) (Ioo (0 : ℝ) 1) :=
    integrableOn_continuous_mul hw (continuous_const.mul continuous_id).continuousOn
  unfold realStieltjes
  rw [← integral_const_mul, ← integral_add (integrableOn_stieltjes hi hz) hw]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  have hne := hz x ⟨hx.1.le, hx.2.le⟩
  dsimp only
  field_simp
  ring

 

theorem polynomial_mul_realStieltjes {a : ℝ} {w : ℝ → ℝ}
    (hw : IntegrableOn w (Ioo (0 : ℝ) 1)) (p : Polynomial ℝ) :
    ∃ R : Polynomial ℝ, ∀ z : ℝ, offCut a z →
      p.eval z * realStieltjes a w z =
        realStieltjes a (fun x => p.eval (a * x) * w x) z + R.eval z := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨R, hR⟩ := hp
      obtain ⟨S, hS⟩ := hq
      refine ⟨R + S, fun z hz => ?_⟩
      simp only [Polynomial.eval_add, add_mul]
      rw [realStieltjes_add (integrableOn_polynomial_weight hw p)
        (integrableOn_polynomial_weight hw q) hz, hR z hz, hS z hz]
      ring
  | monomial n c =>
      induction n with
      | zero =>
          refine ⟨0, fun z hz => ?_⟩
          simp [realStieltjes_const_mul]
      | succ n ih =>
          obtain ⟨R, hR⟩ := ih
          let v : ℝ → ℝ := fun x => c * (a * x) ^ n * w x
          have hv : IntegrableOn v (Ioo (0 : ℝ) 1) := by
            simpa [v] using integrableOn_polynomial_weight hw (Polynomial.monomial n c)
          refine ⟨Polynomial.X * R + Polynomial.C (∫ x in Ioo (0 : ℝ) 1, v x), fun z hz => ?_⟩
          have hrec := realStieltjes_mul_variable hv hz
          have hpoly := hR z hz
          simp only [Polynomial.eval_monomial] at hpoly ⊢
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
            Polynomial.eval_C]
          have heq : (fun x => a * x * v x) = fun x => c * (a * x) ^ (n + 1) * w x := by
            funext x
            simp only [v, pow_succ]
            ring
          rw [heq] at hrec
          change c * z ^ n * realStieltjes a w z = realStieltjes a v z + R.eval z at hpoly
          rw [pow_succ]
          linear_combination z * hpoly + hrec

theorem abs_mul_le_one {a x : ℝ} (ha : |a| ≤ 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    |a * x| ≤ 1 := by
  rw [abs_mul, abs_of_nonneg hx.1]
  nlinarith [abs_nonneg a, hx.1, hx.2]

theorem offCut_of_abs_large {a z : ℝ} (ha : |a| ≤ 1) (hz : 2 ≤ |z|) :
    offCut a z := by
  intro x hx heq
  have h := abs_mul_le_one ha hx
  have hzx : z = a * x := sub_eq_zero.1 heq
  rw [hzx] at hz
  linarith

theorem norm_realStieltjes_le {a z : ℝ} {w : ℝ → ℝ}
    (hw : IntegrableOn w (Ioo (0 : ℝ) 1)) (ha : |a| ≤ 1) (hz : 2 ≤ |z|) :
    ‖realStieltjes a w z‖ ≤ (∫ x in Ioo (0 : ℝ) 1, ‖w x‖) / (|z| - 1) := by
  have hd : 0 < |z| - 1 := by linarith
  have hi := hw.norm.div_const (|z| - 1)
  have hbound : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1),
      ‖w x / (z - a * x)‖ ≤ ‖w x‖ / (|z| - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hax := abs_mul_le_one ha ⟨hx.1.le, hx.2.le⟩
    have hden : |z| - 1 ≤ |z - a * x| := by
      have h := abs_sub_abs_le_abs_sub z (a * x)
      linarith
    rw [norm_div, Real.norm_eq_abs (z - a * x)]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hd hden
  have h := norm_integral_le_of_norm_le hi hbound
  simpa only [realStieltjes, integral_div] using h

end
end CriticalStrip

end OAI
