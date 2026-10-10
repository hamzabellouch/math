import Mathlib
import OAI.Computability.QuantumFactoring.QuantumCore

namespace OAI

section

namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators
open MeasureTheory intervalIntegral

lemma phase_bin_progression {Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d) (j t i : ℕ) :
    phase ((bin Q d j : ℝ)*(t+i*d)/Q) =
      phase (((j*t)%d : ℕ)/ (d:ℝ) + binError Q d j*((t+i*d : ℕ):ℝ)/Q) := by
  have hd' : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hQ' : (Q:ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hr : (((j*t)%d : ℕ):ℝ) + (d:ℝ)*(((j*t)/d : ℕ):ℝ) = (j:ℝ)*t := by
    exact_mod_cast Nat.mod_add_div (j*t) d
  have hjt : (j:ℝ)*t/d = (((j*t)%d : ℕ):ℝ)/d + (((j*t)/d : ℕ):ℝ) := by
    rw [← hr, add_div, mul_div_cancel_left₀ _ hd']
  have heq : (bin Q d j : ℝ)*(t+i*d)/Q =
      (((j*t)%d : ℕ):ℝ)/d + binError Q d j*((t+i*d : ℕ):ℝ)/Q +
      (((j*t/d+j*i : ℕ):ℤ):ℝ) := by
    calc
      _ = (j:ℝ)*t/d+(j:ℝ)*i + binError Q d j*((t+i*d : ℕ):ℝ)/Q := by
        unfold binError
        push_cast
        field_simp
        ring
      _ = _ := by
        rw [hjt]
        simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_add, Nat.cast_mul]
        ring
  rw [heq, phase_add_int]

/-- Equation (order-P), before squaring the norm. -/
noncomputable def residueAmplitude (Q d j t : ℕ) : ℂ :=
  (Q:ℂ)⁻¹ * ∑ x ∈ (Finset.range Q).filter (fun x => x%d=t),
    phase ((bin Q d j:ℝ)*x/Q)

noncomputable def residueProbability (Q d j t : ℕ) : ℝ :=
  ‖residueAmplitude Q d j t‖^2

lemma residueAmplitude_samples {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q)
    (ht : t < d) (j : ℕ) :
    residueAmplitude Q d j t = (Q:ℂ)⁻¹ *
      ∑ i ∈ Finset.range (sampleCount Q d t),
        phase (((j*t)%d : ℕ)/(d:ℝ) +
          binError Q d j*((t:ℝ)/Q+(i:ℝ)*((d:ℝ)/Q))) := by
  have hQ : 0 < Q := lt_of_lt_of_le hd hdQ
  unfold residueAmplitude
  rw [← sum_progression (fun x => phase ((bin Q d j:ℝ)*x/Q)) hd hdQ ht]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.cast_add, Nat.cast_mul, phase_bin_progression hQ hd]
  congr 1
  push_cast
  ring

lemma residueAmplitude_integral_error {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q)
    (ht : t < d) (j : ℕ) :
    ‖residueAmplitude Q d j t - residueIntegral d (((j*t)%d : ℕ):ℝ) (binError Q d j)‖ ≤
      6/(Q:ℝ) := by
  have hQ : 0 < Q := lt_of_lt_of_le hd hdQ
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  let a : ℝ := t/Q
  let h : ℝ := d/Q
  let M := sampleCount Q d t
  let f : ℝ → ℂ := fun v => phase (((j*t)%d : ℕ)/(d:ℝ) + binError Q d j*v)
  have hh₀ : 0 ≤ h := div_nonneg hd'.le hQ'.le
  have hh₁ : h ≤ 1 := (div_le_one hQ').mpr (by exact_mod_cast hdQ)
  have ha₀ : 0 ≤ a := div_nonneg (Nat.cast_nonneg _) hQ'.le
  have ha₁ : a ≤ h := (div_le_div_iff_of_pos_right hQ').mpr (by exact_mod_cast ht.le)
  have he : a+(M:ℝ)*h = ((t+M*d : ℕ):ℝ)/Q := by dsimp [a,h]; push_cast; ring
  have hM := sampleCount_bounds hd hdQ ht
  have hM₀ : 1 ≤ a+(M:ℝ)*h := by
    rw [he]
    apply (one_le_div hQ').mpr
    exact_mod_cast hM.1
  have hM₁ : a+(M:ℝ)*h ≤ 1+h := by
    rw [he]
    have hsum : (1:ℝ)+h = ((Q+d : ℕ):ℝ)/Q := by dsimp [h]; push_cast; field_simp
    rw [hsum]
    apply (div_le_div_iff_of_pos_right hQ').mpr
    exact_mod_cast hM.2
  have hf : Continuous f := phase_continuous.comp (by fun_prop)
  have hL : ∀ v w, ‖f v-f w‖ ≤ 4*|v-w| :=
    segment_phase_sub_le _ (binError_bound hd)
  have hb : ∀ v, ‖f v‖ ≤ 1 := fun v => phase_norm_le _
  have hr := rectangle_sum_unit_error hf hL hb hh₀ hh₁ ha₀ ha₁ M hM₀ hM₁
  have heq : residueAmplitude Q d j t - residueIntegral d (((j*t)%d : ℕ):ℝ) (binError Q d j) =
      (d:ℂ)⁻¹ * (h • (∑ i ∈ Finset.range M, f (a+i*h)) - ∫ v in (0:ℝ)..1, f v) := by
    rw [residueAmplitude_samples hd hdQ ht]
    dsimp [residueIntegral, averagePhase, f, a, h, M]
    push_cast
    have hdC : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hQC : (Q:ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
    field_simp
  rw [heq, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (d:ℝ)⁻¹*(6*h) := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr hd'.le)
    _ = 6/(Q:ℝ) := by dsimp [h]; field_simp

lemma residueAmplitude_norm_le {Q : ℕ} (hQ : 0 < Q) (d j t : ℕ) :
    ‖residueAmplitude Q d j t‖ ≤ 1 := by
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  let s := (Finset.range Q).filter (fun x => x%d=t)
  have hc : (s.card:ℝ) ≤ Q := by exact_mod_cast (Finset.card_filter_le (s := Finset.range Q)
    (p := fun x => x%d=t) |>.trans_eq (Finset.card_range Q))
  rw [residueAmplitude, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Q:ℝ)⁻¹*∑ x ∈ s, ‖phase ((bin Q d j:ℝ)*x/Q)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hQ'.le)
    _ ≤ (Q:ℝ)⁻¹*∑ _x ∈ s, (1:ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => phase_norm_le _))
        (inv_nonneg.mpr hQ'.le)
    _ ≤ (Q:ℝ)⁻¹*Q := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr hQ'.le)
    _ = 1 := inv_mul_cancel₀ hQ'.ne'

lemma norm_square_difference_le {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    |‖z‖^2-‖w‖^2| ≤ 2*‖z-w‖ := by
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  have h := abs_norm_sub_norm_le z w
  exact mul_le_mul (show ‖z‖+‖w‖ ≤ 2 by linarith) h (abs_nonneg _) (by norm_num)

/-- The key approximation (majorant-integral-bounds), for the exact source P. -/
lemma residueProbability_integral_error {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q)
    (ht : t < d) (j : ℕ) :
    |residueProbability Q d j t -
      ‖residueIntegral d (((j*t)%d : ℕ):ℝ) (binError Q d j)‖^2| ≤ 32/(Q:ℝ) := by
  have hQ : 0 < Q := lt_of_lt_of_le hd hdQ
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hI := (residueIntegral_bounds hd (((j*t)%d : ℕ):ℝ) (binError_bound (Q := Q) (j := j) hd)).2
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hI₁ : ‖residueIntegral d (((j*t)%d : ℕ):ℝ) (binError Q d j)‖ ≤ 1 :=
    hI.trans ((div_le_one (lt_of_lt_of_le zero_lt_one hd')).mpr hd')
  have h := norm_square_difference_le (residueAmplitude_norm_le hQ d j t) hI₁
  have he := residueAmplitude_integral_error hd hdQ ht j
  unfold residueProbability
  calc
    _ ≤ 2*‖residueAmplitude Q d j t - residueIntegral d (((j*t)%d : ℕ):ℝ) (binError Q d j)‖ := h
    _ ≤ 2*(6/(Q:ℝ)) := mul_le_mul_of_nonneg_left he (by norm_num)
    _ ≤ 32/(Q:ℝ) := by apply (le_div_iff₀ hQ').mpr; field_simp; norm_num

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators Topology
open Set Filter

/-- A positive-part square. This supplies a globally C¹ rational spline primitive. -/
noncomputable def rampSq (x : ℝ) : ℝ := (max 0 x)^2

lemma rampSq_hasDerivAt (x : ℝ) : HasDerivAt rampSq (2*max 0 x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have he : rampSq =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
      filter_upwards [eventually_lt_nhds hx] with y hy
      simp [rampSq, max_eq_left hy.le]
    simpa only [max_eq_left hx.le, mul_zero] using!
      (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq he
  · have hl : HasDerivWithinAt rampSq 0 (Iic 0) 0 := by
      apply (hasDerivAt_const (0:ℝ) (0:ℝ)).hasDerivWithinAt.congr
      · intro y hy
        simp [rampSq, max_eq_left (show y ≤ 0 from hy)]
      · norm_num [rampSq]
    have hr : HasDerivWithinAt rampSq 0 (Ici 0) 0 := by
      have h : HasDerivAt (fun y : ℝ => y^2) 0 0 := by
        simpa using! (hasDerivAt_id (0:ℝ)).pow 2
      apply h.hasDerivWithinAt.congr
      · intro y hy
        simp only [rampSq, max_eq_right (show 0 ≤ y from hy)]
      · norm_num [rampSq]
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ, max_self, mul_zero] using hl.union hr
  · have he : rampSq =ᶠ[𝓝 x] fun y => y^2 := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      simp only [rampSq, max_eq_right hy.le]
    simpa [max_eq_right hx.le] using!
      ((hasDerivAt_id x).pow 2).congr_of_eventuallyEq he

lemma rampSq_continuous : Continuous rampSq := by
  unfold rampSq
  fun_prop

lemma rampSq_shift_hasDerivAt (x a : ℝ) :
    HasDerivAt (fun y => rampSq (y-a)) (2*max 0 (x-a)) x := by
  simpa only [mul_one] using!
    (rampSq_hasDerivAt (x-a)).comp x ((hasDerivAt_id x).sub_const a)

noncomputable def splineRe (x : ℝ) : ℝ :=
  -(x+1/2)+2*(x+1/2)^2-4*rampSq x+4*rampSq (x-1/2)-4*rampSq (x-1)

noncomputable def splineIm (x : ℝ) : ℝ :=
  2*(x+1/2)^2-4*rampSq (x+1/4)+4*rampSq (x-1/4)-
    4*rampSq (x-3/4)+4*rampSq (x-5/4)-1/4

noncomputable def splineReDeriv (x : ℝ) : ℝ :=
  -1+4*(x+1/2)-8*max 0 x+8*max 0 (x-1/2)-8*max 0 (x-1)

noncomputable def splineImDeriv (x : ℝ) : ℝ :=
  4*(x+1/2)-8*max 0 (x+1/4)+8*max 0 (x-1/4)-
    8*max 0 (x-3/4)+8*max 0 (x-5/4)

lemma splineRe_hasDerivAt (x : ℝ) : HasDerivAt splineRe (splineReDeriv x) x := by
  have h := (hasDerivAt_id x).add_const (1/2:ℝ)
  have h₀ := rampSq_hasDerivAt x
  have h₁ := rampSq_shift_hasDerivAt x (1/2)
  have h₂ := rampSq_shift_hasDerivAt x 1
  convert! ((((h.neg.add ((h.pow 2).const_mul 2)).sub (h₀.const_mul 4)).add
    (h₁.const_mul 4)).sub (h₂.const_mul 4)) using 1
  simp [splineReDeriv]
  ring

lemma splineIm_hasDerivAt (x : ℝ) : HasDerivAt splineIm (splineImDeriv x) x := by
  have h := (hasDerivAt_id x).add_const (1/2:ℝ)
  have h₀ : HasDerivAt (fun y => rampSq (y+1/4)) (2*max 0 (x+1/4)) x := by
    simpa only [mul_one] using!
      (rampSq_hasDerivAt (x+1/4)).comp x ((hasDerivAt_id x).add_const (1/4:ℝ))
  have h₁ := rampSq_shift_hasDerivAt x (1/4)
  have h₂ := rampSq_shift_hasDerivAt x (3/4)
  have h₃ := rampSq_shift_hasDerivAt x (5/4)
  convert! ((((((h.pow 2).const_mul 2).sub (h₀.const_mul 4)).add (h₁.const_mul 4)).sub
    (h₂.const_mul 4)).add (h₃.const_mul 4)).sub_const (1/4:ℝ) using 1
  simp [splineImDeriv]
  ring

noncomputable def spline (x : ℝ) : ℂ := (splineRe x : ℂ) + (splineIm x : ℂ)*Complex.I

lemma spline_hasDerivAt (x : ℝ) :
    HasDerivAt spline ((splineReDeriv x : ℂ)+(splineImDeriv x : ℂ)*Complex.I) x :=
  (splineRe_hasDerivAt x).ofReal_comp.add ((splineIm_hasDerivAt x).ofReal_comp.mul_const _)

end ExactQuantumFactoring.OrderTrial

namespace ExactQuantumFactoring.OrderTrial
open MeasureTheory intervalIntegral

lemma splineReDeriv_eq {x : ℝ} (hx₀ : -(1/2) ≤ x) (hx₁ : x ≤ 3/2) :
    splineReDeriv x = triangle x := by
  unfold splineReDeriv
  by_cases h₀ : x ≤ 0
  · rw [max_eq_left h₀, max_eq_left (by linarith : x-1/2 ≤ 0),
      max_eq_left (by linarith : x-1 ≤ 0), triangle_local (by rw [abs_le]; constructor <;> linarith),
      abs_of_nonpos h₀]
    ring
  · have h₀' := le_of_not_ge h₀
    rw [max_eq_right h₀']
    by_cases h₁ : x ≤ 1/2
    · rw [max_eq_left (by linarith : x-1/2 ≤ 0), max_eq_left (by linarith : x-1 ≤ 0),
        triangle_local (by rw [abs_le]; constructor <;> linarith), abs_of_nonneg h₀']
      ring
    · have ht : triangle x = triangle (x-1) := by
        convert triangle_add_int (x-1) 1 using 1
        norm_num
      rw [ht, triangle_local (by rw [abs_le]; constructor <;> linarith),
        max_eq_right (by linarith : 0 ≤ x-1/2)]
      by_cases h₂ : x ≤ 1
      · rw [max_eq_left (by linarith : x-1 ≤ 0), abs_of_nonpos (by linarith : x-1 ≤ 0)]
        ring
      · rw [max_eq_right (by linarith : 0 ≤ x-1), abs_of_nonneg (by linarith : 0 ≤ x-1)]
        ring

lemma splineImDeriv_eq {x : ℝ} (hx₀ : -(1/2) ≤ x) (hx₁ : x ≤ 3/2) :
    splineImDeriv x = -triangle (x-1/4) := by
  unfold splineImDeriv
  by_cases h₀ : x ≤ -(1/4)
  · have ht : triangle (x-1/4) = triangle (x+3/4) := by
      symm
      convert triangle_add_int (x-1/4) 1 using 1
      norm_num
      congr 1
      ring
    rw [max_eq_left (by linarith : x+1/4 ≤ 0),
      max_eq_left (by linarith : x-1/4 ≤ 0), max_eq_left (by linarith : x-3/4 ≤ 0),
      max_eq_left (by linarith : x-5/4 ≤ 0), ht,
      triangle_local (by rw [abs_le]; constructor <;> linarith),
      abs_of_nonneg (by linarith : 0 ≤ x+3/4)]
    ring
  · rw [max_eq_right (by linarith : 0 ≤ x+1/4)]
    by_cases h₁ : x ≤ 1/4
    · rw [max_eq_left (by linarith : x-1/4 ≤ 0), max_eq_left (by linarith : x-3/4 ≤ 0),
        max_eq_left (by linarith : x-5/4 ≤ 0),
        triangle_local (by rw [abs_le]; constructor <;> linarith),
        abs_of_nonpos (by linarith : x-1/4 ≤ 0)]
      ring
    · rw [max_eq_right (by linarith : 0 ≤ x-1/4)]
      by_cases h₂ : x ≤ 3/4
      · rw [max_eq_left (by linarith : x-3/4 ≤ 0), max_eq_left (by linarith : x-5/4 ≤ 0),
          triangle_local (by rw [abs_le]; constructor <;> linarith),
          abs_of_nonneg (by linarith : 0 ≤ x-1/4)]
        ring
      · have ht : triangle (x-1/4) = triangle (x-5/4) := by
          convert triangle_add_int (x-5/4) 1 using 1
          norm_num
          congr 1
          ring
        rw [max_eq_right (by linarith : 0 ≤ x-3/4), ht,
          triangle_local (by rw [abs_le]; constructor <;> linarith)]
        by_cases h₃ : x ≤ 5/4
        · rw [max_eq_left (by linarith : x-5/4 ≤ 0), abs_of_nonpos (by linarith : x-5/4 ≤ 0)]
          ring
        · rw [max_eq_right (by linarith : 0 ≤ x-5/4), abs_of_nonneg (by linarith : 0 ≤ x-5/4)]
          ring

lemma spline_derivative {x : ℝ} (hx₀ : -(1/2) ≤ x) (hx₁ : x ≤ 3/2) :
    HasDerivAt spline (phase x) x := by
  have h := spline_hasDerivAt x
  rw [splineReDeriv_eq hx₀ hx₁, splineImDeriv_eq hx₀ hx₁] at h
  convert! h using 1
  apply Complex.ext <;> simp [phase]

lemma spline_zero : spline 0 = 0 := by
  norm_num [spline, splineRe, splineIm, rampSq]

lemma spline_integral {a b : ℝ} (ha₀ : -(1/2) ≤ a) (ha₁ : a ≤ 3/2)
    (hb₀ : -(1/2) ≤ b) (hb₁ : b ≤ 3/2) :
    (∫ v in a..b, phase v) = spline b-spline a := by
  apply integral_eq_sub_of_hasDerivAt _ (phase_continuous.intervalIntegrable _ _)
  intro x hx
  obtain ⟨hl,hu⟩ := hx
  apply spline_derivative
  · exact (le_min ha₀ hb₀).trans hl
  · exact hu.trans (max_le ha₁ hb₁)

end ExactQuantumFactoring.OrderTrial

namespace ExactQuantumFactoring.OrderTrial
open scoped Polynomial
open Polynomial MeasureTheory intervalIntegral

/-- Rational polynomial on a quarter interval; no real oracle is used in its data. -/
noncomputable def rampPiece (q a : ℤ) : ℚ[X] :=
  if a ≤ q then (X-C ((a:ℚ)/4))^2 else 0

noncomputable def evalReal (p : ℚ[X]) (x : ℝ) : ℝ := p.eval₂ (Rat.castHom ℝ) x

lemma evalReal_rampPiece (q a : ℤ) {x : ℝ} (h₀ : (q:ℝ)/4 ≤ x)
    (h₁ : x ≤ ((q:ℝ)+1)/4) :
    evalReal (rampPiece q a) x = rampSq (x-(a:ℝ)/4) := by
  by_cases h : a ≤ q
  · have h' : (a:ℝ) ≤ q := by exact_mod_cast h
    have hx : 0 ≤ x-(a:ℝ)/4 := by linarith
    simp only [rampPiece, ite_eq_left h, evalReal, Polynomial.eval₂_pow,
      Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, rampSq, max_eq_right hx]
    norm_num
  · have h' : (q:ℝ)+1 ≤ a := by exact_mod_cast (show q+1 ≤ a by omega)
    have hx : x-(a:ℝ)/4 ≤ 0 := by linarith
    simp [rampPiece, h, evalReal, rampSq, max_eq_left hx]

noncomputable def splineRePiece (q : ℤ) : ℚ[X] :=
  -(X+C (1/2))+ C 2*(X+C (1/2))^2 - C 4*rampPiece q 0 +
    C 4*rampPiece q 2 - C 4*rampPiece q 4

noncomputable def splineImPiece (q : ℤ) : ℚ[X] :=
  C 2*(X+C (1/2))^2-C 4*rampPiece q (-1)+C 4*rampPiece q 1-
    C 4*rampPiece q 3+C 4*rampPiece q 5-C (1/4)

lemma evalReal_splineRePiece (q : ℤ) {x : ℝ} (h₀ : (q:ℝ)/4 ≤ x)
    (h₁ : x ≤ ((q:ℝ)+1)/4) : evalReal (splineRePiece q) x = splineRe x := by
  have h0 := evalReal_rampPiece q 0 h₀ h₁
  have h2 := evalReal_rampPiece q 2 h₀ h₁
  have h4 := evalReal_rampPiece q 4 h₀ h₁
  simp only [evalReal, splineRePiece, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_neg, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X]
  change -(x+(1/2:ℚ))+ (2:ℚ)*(x+(1/2:ℚ))^2 - (4:ℚ)*evalReal (rampPiece q 0) x +
    (4:ℚ)*evalReal (rampPiece q 2) x - (4:ℚ)*evalReal (rampPiece q 4) x = splineRe x
  rw [h0,h2,h4]
  norm_num [splineRe]

lemma evalReal_splineImPiece (q : ℤ) {x : ℝ} (h₀ : (q:ℝ)/4 ≤ x)
    (h₁ : x ≤ ((q:ℝ)+1)/4) : evalReal (splineImPiece q) x = splineIm x := by
  have hm1 := evalReal_rampPiece q (-1) h₀ h₁
  have h1 := evalReal_rampPiece q 1 h₀ h₁
  have h3 := evalReal_rampPiece q 3 h₀ h₁
  have h5 := evalReal_rampPiece q 5 h₀ h₁
  simp only [evalReal, splineImPiece, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C,
    Polynomial.eval₂_X]
  change (2:ℚ)*(x+(1/2:ℚ))^2 - (4:ℚ)*evalReal (rampPiece q (-1)) x +
    (4:ℚ)*evalReal (rampPiece q 1) x - (4:ℚ)*evalReal (rampPiece q 3) x +
    (4:ℚ)*evalReal (rampPiece q 5) x - (1/4:ℚ) = splineIm x
  rw [hm1,h1,h3,h5]
  norm_num [splineIm]

lemma poly_add_degree {p q : ℚ[X]} {k : ℕ} (hp : p.natDegree ≤ k) (hq : q.natDegree ≤ k) :
    (p+q).natDegree ≤ k := (natDegree_add_le _ _).trans (max_le hp hq)

lemma poly_sub_degree {p q : ℚ[X]} {k : ℕ} (hp : p.natDegree ≤ k) (hq : q.natDegree ≤ k) :
    (p-q).natDegree ≤ k := (natDegree_sub_le _ _).trans (max_le hp hq)

lemma rampPiece_natDegree_le (q a : ℤ) : (rampPiece q a).natDegree ≤ 2 := by
  unfold rampPiece
  split_ifs
  · apply le_trans (Polynomial.natDegree_pow_le)
    have h : (X-C ((a:ℚ)/4)).natDegree ≤ 1 :=
      le_trans (Polynomial.natDegree_sub_le _ _) (by simp)
    omega
  · simp

lemma splineRePiece_natDegree_le (q : ℤ) : (splineRePiece q).natDegree ≤ 2 := by
  have hX : (X+C (1/2:ℚ)).natDegree ≤ 1 :=
    le_trans (Polynomial.natDegree_add_le _ _) (by simp)
  have hSq : ((X+C (1/2:ℚ))^2).natDegree ≤ 2 :=
    (Polynomial.natDegree_pow_le).trans (by omega)
  unfold splineRePiece
  apply poly_sub_degree
  · apply poly_add_degree
    · apply poly_sub_degree
      · apply poly_add_degree
        · simpa only [natDegree_neg] using (hX.trans (by norm_num : 1 ≤ 2))
        · exact (natDegree_C_mul_le _ _).trans hSq
      · exact (natDegree_C_mul_le _ _).trans (rampPiece_natDegree_le _ _)
    · exact (natDegree_C_mul_le _ _).trans (rampPiece_natDegree_le _ _)
  · exact (natDegree_C_mul_le _ _).trans (rampPiece_natDegree_le _ _)

lemma splineImPiece_natDegree_le (q : ℤ) : (splineImPiece q).natDegree ≤ 2 := by
  have hX : (X+C (1/2:ℚ)).natDegree ≤ 1 :=
    le_trans (Polynomial.natDegree_add_le _ _) (by simp)
  have hSq : ((X+C (1/2:ℚ))^2).natDegree ≤ 2 :=
    (Polynomial.natDegree_pow_le).trans (by omega)
  unfold splineImPiece
  apply poly_sub_degree
  · apply poly_add_degree
    · apply poly_sub_degree
      · apply poly_add_degree
        · apply poly_sub_degree
          · exact (natDegree_C_mul_le _ _).trans hSq
          · exact (natDegree_C_mul_le _ _).trans (rampPiece_natDegree_le _ _)
        · exact (natDegree_C_mul_le _ _).trans (rampPiece_natDegree_le _ _)
      · exact (natDegree_C_mul_le _ _).trans (rampPiece_natDegree_le _ _)
    · exact (natDegree_C_mul_le _ _).trans (rampPiece_natDegree_le _ _)
  · simp

end ExactQuantumFactoring.OrderTrial


end

end OAI
