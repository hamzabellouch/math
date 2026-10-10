import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

namespace Problem336

theorem norm_exp_imaginary_taylor_two_le (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I +
      (x : ℂ) ^ 2 / 2‖ ≤ 4 * |x| ^ 3 := by
  have hnorm : ‖(x : ℂ) * Complex.I‖ = |x| := by simp
  by_cases hx : |x| ≤ 1
  · have hb := Complex.exp_bound (x := (x : ℂ) * Complex.I)
      (by simpa only [hnorm] using hx) (n := 3) (by decide)
    have heq : (∑ m ∈ Finset.range 3,
        ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)) =
        1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2 := by
      norm_num [Finset.sum_range_succ, mul_pow, Complex.I_sq]
      ring
    rw [heq, hnorm] at hb
    have hn : 0 ≤ |x| ^ 3 := by positivity
    norm_num at hb
    calc
      _ = ‖Complex.exp ((x : ℂ) * Complex.I) -
          (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2)‖ := by congr 1; ring
      _ ≤ 4 * |x| ^ 3 := by linarith
  · have hx1 : 1 ≤ |x| := le_of_lt (lt_of_not_ge hx)
    have hbound :
        ‖Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I +
          (x : ℂ) ^ 2 / 2‖ ≤ 2 + |x| + |x| ^ 2 / 2 := by
      calc
        _ ≤ ‖Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I‖ +
            ‖(x : ℂ) ^ 2 / 2‖ := norm_add_le _ _
        _ ≤ (‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ +
            ‖(x : ℂ) * Complex.I‖) + ‖(x : ℂ) ^ 2 / 2‖ :=
          by
          gcongr
          exact norm_sub_le _ _
        _ ≤ ((‖Complex.exp ((x : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖) +
            ‖(x : ℂ) * Complex.I‖) + ‖(x : ℂ) ^ 2 / 2‖ := by
          gcongr
          exact norm_sub_le _ _
        _ = 2 + |x| + |x| ^ 2 / 2 := by
          simp [Complex.norm_exp_ofReal_mul_I, norm_pow]
          ring
    have hsq : |x| ≤ |x| ^ 2 := by nlinarith [abs_nonneg x]
    have hcube : |x| ^ 2 ≤ |x| ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg |x|) (sub_nonneg.mpr hx1)]
    nlinarith

theorem characteristic_taylor_two_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {D : Ω → ℝ}
    (hD : Integrable D P) (hD2 : Integrable (fun ω => D ω ^ 2) P)
    (hD3 : Integrable (fun ω => |D ω| ^ 3) P) :
    ‖(∫ ω, Complex.exp ((D ω : ℂ) * Complex.I) ∂P) -
      ((P.real Set.univ : ℂ) + (∫ ω, D ω ∂P : ℝ) * Complex.I -
        (∫ ω, D ω ^ 2 ∂P : ℝ) / 2)‖ ≤ 4 * ∫ ω, |D ω| ^ 3 ∂P := by
  have hm : AEStronglyMeasurable
      (fun ω => Complex.exp ((D ω : ℂ) * Complex.I)) P :=
    (show Continuous (fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I)) by
      fun_prop).comp_aestronglyMeasurable hD.aestronglyMeasurable
  have hc : Integrable (fun ω => Complex.exp ((D ω : ℂ) * Complex.I)) P :=
    Integrable.of_bound hm 1 (Eventually.of_forall (fun ω => by simp))
  have hl : Integrable (fun ω => (D ω : ℂ) * Complex.I) P :=
    hD.ofReal.mul_const Complex.I
  have hq : Integrable (fun ω => (D ω : ℂ) ^ 2 / 2) P := by
    have hq0 : Integrable (fun ω => ((D ω ^ 2 : ℝ) : ℂ)) P := hD2.ofReal
    convert hq0.div_const (2 : ℂ) using 1
    ext ω
    push_cast
    rfl
  let R : Ω → ℂ := fun ω => Complex.exp ((D ω : ℂ) * Complex.I) - 1 -
    (D ω : ℂ) * Complex.I + (D ω : ℂ) ^ 2 / 2
  have hR : Integrable R P := ((hc.sub (integrable_const 1)).sub hl).add hq
  have hRI : (∫ ω, R ω ∂P) =
      (∫ ω, Complex.exp ((D ω : ℂ) * Complex.I) ∂P) -
      ((P.real Set.univ : ℂ) + (∫ ω, D ω ∂P : ℝ) * Complex.I -
        (∫ ω, D ω ^ 2 ∂P : ℝ) / 2) := by
    dsimp [R]
    have hs : Integrable (fun ω => Complex.exp ((D ω : ℂ) * Complex.I) - 1 -
        (D ω : ℂ) * Complex.I) P := (hc.sub (integrable_const 1)).sub hl
    have hs' : Integrable (fun ω => Complex.exp ((D ω : ℂ) * Complex.I) - 1) P :=
      hc.sub (integrable_const 1)
    rw [integral_add hs hq, integral_sub hs' hl,
      integral_sub hc (integrable_const 1), integral_const,
      integral_mul_const, integral_div, integral_complex_ofReal]
    simp only [← Complex.ofReal_pow, integral_complex_ofReal,
      Complex.real_smul, mul_one]
    ring
  rw [← hRI]
  calc
    ‖∫ ω, R ω ∂P‖ ≤ ∫ ω, ‖R ω‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, 4 * |D ω| ^ 3 ∂P :=
      integral_mono_ae hR.norm (hD3.const_mul 4)
        (Eventually.of_forall (fun ω => norm_exp_imaginary_taylor_two_le (D ω)))
    _ = 4 * ∫ ω, |D ω| ^ 3 ∂P := integral_const_mul _ _

end Problem336

end

end OAI
