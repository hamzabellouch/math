import Mathlib

namespace OAI

section


/-! Exact integer arithmetic for the prescribed-mass order trial.
These are dependencies of the actual main theorem, not assumptions about an
unknown order and not a replacement target. -/
namespace ExactQuantumFactoring.OrderTrial

open scoped BigOperators

/-- Number of integers x<Q congruent to t modulo d, when t<d≤Q. -/
def sampleCount (Q d t : ℕ) : ℕ := (Q-1-t)/d+1

lemma sampleCount_bounds {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q) (ht : t < d) :
    Q ≤ t+sampleCount Q d t*d ∧ t+sampleCount Q d t*d ≤ Q+d := by
  have htQ : t < Q := lt_of_lt_of_le ht hdQ
  have hr := Nat.mod_lt (Q-1-t) hd
  have heq : (Q-1-t)%d + ((Q-1-t)/d)*d = Q-1-t := by
    simpa only [Nat.mul_comm] using Nat.mod_add_div (Q-1-t) d
  unfold sampleCount
  rw [Nat.add_mul, one_mul]
  omega

lemma lt_sampleCount_iff {Q d t i : ℕ} (hd : 0 < d) (hdQ : d ≤ Q) (ht : t < d) :
    i < sampleCount Q d t ↔ t+i*d < Q := by
  have htQ : t < Q := lt_of_lt_of_le ht hdQ
  unfold sampleCount
  rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hd]
  omega

lemma sum_progression {α : Type*} [AddCommMonoid α] (f : ℕ → α)
    {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q) (ht : t < d) :
    (∑ i ∈ Finset.range (sampleCount Q d t), f (t+i*d)) =
      ∑ x ∈ (Finset.range Q).filter (fun x => x%d=t), f x := by
  apply Finset.sum_bij (fun i _ => t+i*d)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at *
    refine ⟨(lt_sampleCount_iff hd hdQ ht).mp hi, ?_⟩
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  · intro i hi j hj heq
    exact Nat.mul_right_cancel hd (Nat.add_left_cancel heq)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    have heq : t+(x/d)*d=x := by
      have h := Nat.mod_add_div x d
      rw [hx.2] at h
      simpa only [Nat.mul_comm] using h
    refine ⟨x/d, ?_, heq⟩
    rw [Finset.mem_range, lt_sampleCount_iff hd hdQ ht, heq]
    exact hx.1
  · intro i hi
    rfl

/-- Literal nearest-bin rule floor(jQ/d+1/2), expressed entirely with integers. -/
def bin (Q d j : ℕ) : ℕ := (2*j*Q+d)/(2*d)

noncomputable def binError (Q d j : ℕ) : ℝ := (bin Q d j : ℝ) - (j:ℝ)*Q/d

lemma binError_bound {Q d j : ℕ} (hd : 0 < d) : |binError Q d j| ≤ 1/2 := by
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have h₁ : bin Q d j*(2*d) ≤ 2*j*Q+d := Nat.div_mul_le_self _ _
  have h₂ : 2*j*Q+d < (bin Q d j+1)*(2*d) := by
    have hr := Nat.mod_lt (2*j*Q+d) (by omega : 0 < 2*d)
    have heq := Nat.mod_add_div (2*j*Q+d) (2*d)
    change (2*j*Q+d)%(2*d) + (2*d)*bin Q d j = 2*j*Q+d at heq
    nlinarith
  have h₁' : (bin Q d j:ℝ)*(2*d) ≤ 2*j*Q+d := by exact_mod_cast h₁
  have h₂' : (2:ℝ)*j*Q+d < ((bin Q d j:ℝ)+1)*(2*d) := by exact_mod_cast h₂
  have heq : binError Q d j*(d:ℝ) = (bin Q d j:ℝ)*d-(j:ℝ)*Q := by
    rw [binError, sub_mul, div_mul_cancel₀ _ hd'.ne']
  rw [abs_le]
  constructor
  · apply (mul_le_mul_iff_left₀ hd').mp
    nlinarith
  · apply (mul_le_mul_iff_left₀ hd').mp
    nlinarith

end ExactQuantumFactoring.OrderTrial



/-! Dependencies for the actual prescribed-probability order trial.
The phase below is proved to be exactly the quarter-linear interpolant in
sections/03-order-transform.tex. No oracle/order information is input. -/
namespace ExactQuantumFactoring.OrderTrial

open scoped BigOperators
open MeasureTheory intervalIntegral

/-- Real triangular wave, period one; quotient norm makes continuity explicit. -/
noncomputable def triangle (x : ℝ) : ℝ := 1 - 4 * ‖(x : UnitAddCircle)‖

lemma triangle_local {x : ℝ} (h : |x| ≤ 1/2) : triangle x = 1 - 4 * |x| := by
  unfold triangle
  rw [(AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2 (by simpa using h)]

lemma triangle_add_int (x : ℝ) (k : ℤ) : triangle (x + k) = triangle x := by
  simp only [triangle, UnitAddCircle.norm_eq, round_add_intCast, Int.cast_add]
  congr 2
  ring_nf

lemma triangle_half (x : ℝ) : triangle (x + 1/2) = -triangle x := by
  let y : ℝ := x - round x
  have hy : |y| ≤ 1/2 := abs_sub_round x
  have hx : x = y + round x := by dsimp [y]; ring
  rw [hx]
  rw [show y + (round x : ℝ) + 1/2 = (y+1/2) + round x by ring,
    triangle_add_int, triangle_add_int]
  rcases le_total y 0 with hneg | hpos
  · have hy' : |y + 1/2| ≤ 1/2 := by rw [abs_le] at hy ⊢; constructor <;> linarith
    rw [triangle_local hy, triangle_local hy', abs_of_nonpos hneg,
      abs_of_nonneg (by have := (abs_le.mp hy).1; linarith : 0 ≤ y+1/2)]
    ring
  · have hy' : |y - 1/2| ≤ 1/2 := by rw [abs_le] at hy ⊢; constructor <;> linarith
    rw [show y+1/2 = (y-1/2) + (1 : ℤ) by norm_num; ring,
      triangle_add_int, triangle_local hy, triangle_local hy', abs_of_nonneg hpos,
      abs_of_nonpos (by have := (abs_le.mp hy).2; linarith : y-1/2 ≤ 0)]
    ring

lemma triangle_continuous : Continuous triangle := by
  exact continuous_const.sub (continuous_const.mul
    (AddCircle.continuous_mk' (1 : ℝ)).norm)

/-- Exact polygon phase, with clockwise orientation as in the forward shift. -/
noncomputable def phase (x : ℝ) : ℂ := ⟨triangle x, -triangle (x - 1/4)⟩

lemma phase_continuous : Continuous phase := by
  have h := (Complex.continuous_ofReal.comp triangle_continuous).sub
    ((Complex.continuous_ofReal.comp
      (triangle_continuous.comp (continuous_id.sub (continuous_const (y := (1/4 : ℝ)))))).mul
      (continuous_const (y := Complex.I)))
  convert h using 1
  funext x
  apply Complex.ext <;> simp [phase]

lemma phase_quarter (x : ℝ) : phase (x + 1/4) = -Complex.I * phase x := by
  have h := triangle_half (x - 1/4)
  rw [show x-1/4+1/2 = x+1/4 by ring] at h
  apply Complex.ext
  · simpa only [phase, neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg] using h
  · simp only [phase, neg_mul, Complex.neg_im, Complex.I_mul_im]
    congr 2
    ring

lemma phase_add_int (x : ℝ) (k : ℤ) : phase (x + k) = phase x := by
  apply Complex.ext
  · exact triangle_add_int _ _
  · change -triangle (x + k - 1/4) = -triangle (x-1/4)
    rw [show x + k - 1/4 = (x-1/4)+k by ring, triangle_add_int]

lemma phase_zero_quarter {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    phase (t/4) = (1-t : ℂ) + (t : ℂ) * (-Complex.I) := by
  have ha : |t/4| ≤ 1/2 := by rw [abs_le]; constructor <;> linarith
  have hb : |t/4-1/4| ≤ 1/2 := by rw [abs_le]; constructor <;> linarith
  apply Complex.ext
  · change triangle (t/4) = _
    rw [triangle_local ha, abs_of_nonneg (by positivity : 0 ≤ t/4)]
    simp
    ring
  · change -triangle (t/4-1/4) = _
    rw [triangle_local hb, abs_of_nonpos (by linarith : t/4-1/4 ≤ 0)]
    simp
    ring

lemma triangle_quadratic_lower (x : ℝ) : 1/2 - 8*x^2 ≤ triangle x := by
  have hn : ‖(x : UnitAddCircle)‖ ≤ |x| := by
    rw [UnitAddCircle.norm_eq]
    simpa using round_le x 0
  have hs := sq_nonneg (|x| - 1/4)
  rw [triangle]
  nlinarith [sq_abs x]

lemma phase_add_quarters (x : ℝ) (q : ℤ) :
    phase (x + (q : ℝ)/4) = (-Complex.I)^q * phase x := by
  have hi : (-Complex.I) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
  induction q using Int.induction_on with
  | zero => simp
  | succ q ih =>
      simp only [Int.cast_natCast] at ih
      rw [Int.cast_add, Int.cast_natCast, Int.cast_one,
        show x + ((q : ℝ) + 1)/4 = (x + (q : ℝ)/4) + 1/4 by ring,
        phase_quarter, ih, zpow_add₀ hi]
      simp only [zpow_one]
      ring
  | pred q ih =>
      have h := phase_quarter (x + ((-(q : ℤ)-1 : ℤ) : ℝ)/4)
      rw [show x + ((-(q : ℤ)-1 : ℤ) : ℝ)/4 + 1/4 =
          x + ((-(q : ℤ) : ℤ) : ℝ)/4 by push_cast; ring, ih] at h
      calc
        phase (x + ((-(q : ℤ)-1 : ℤ) : ℝ)/4) =
            (-Complex.I)⁻¹ * ((-Complex.I)^(-(q : ℤ)) * phase x) := by
          rw [h, ← mul_assoc, inv_mul_cancel₀ hi, one_mul]
        _ = (-Complex.I)^(-(q : ℤ)-1) * phase x := by
          rw [show -(q : ℤ)-1 = -(q : ℤ)+(-1) by ring,
            zpow_add₀ hi, zpow_neg_one]
          ring

lemma phase_interpolates (q : ℤ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    phase (((q : ℝ)+t)/4) = (1-t : ℂ)*(-Complex.I)^q +
      (t : ℂ)*(-Complex.I)^(q+1) := by
  rw [show ((q : ℝ)+t)/4 = t/4 + (q : ℝ)/4 by ring,
    phase_add_quarters, phase_zero_quarter ht0 ht1,
    zpow_add₀ (neg_ne_zero.mpr Complex.I_ne_zero)]
  simp only [zpow_one]
  ring

lemma phase_norm_le (x : ℝ) : ‖phase x‖ ≤ 1 := by
  let q : ℤ := ⌊4*x⌋
  let t : ℝ := 4*x-q
  have ht0 : 0 ≤ t := sub_nonneg.mpr (Int.floor_le _)
  have ht1 : t ≤ 1 := by
    have h := Int.lt_floor_add_one (4*x)
    change 4*x - (⌊4*x⌋ : ℝ) ≤ 1
    linarith
  have hx : x = ((q : ℝ)+t)/4 := by dsimp [t]; ring
  rw [hx, phase_interpolates q ht0 ht1]
  calc
    _ ≤ ‖(1-t : ℂ)*(-Complex.I)^q‖ + ‖(t : ℂ)*(-Complex.I)^(q+1)‖ := norm_add_le _ _
    _ = 1 := by
      simp only [norm_mul, norm_zpow, norm_neg, Complex.norm_I, one_zpow, mul_one,
        ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ht0, abs_of_nonneg (sub_nonneg.mpr ht1)]
      ring

lemma triangle_sub_le (x y : ℝ) : |triangle x - triangle y| ≤ 4*|x-y| := by
  have h₁ := abs_norm_sub_norm_le (x : UnitAddCircle) (y : UnitAddCircle)
  have h₂ : ‖(x : UnitAddCircle) - (y : UnitAddCircle)‖ ≤ |x-y| := by
    rw [← QuotientAddGroup.mk_sub, UnitAddCircle.norm_eq]
    simpa using round_le (x-y) 0
  have heq : triangle x - triangle y =
      -4 * (‖(x : UnitAddCircle)‖ - ‖(y : UnitAddCircle)‖) := by
    unfold triangle
    ring
  rw [heq, abs_mul]
  norm_num
  linarith

lemma phase_norm_sub_le (x y : ℝ) : ‖phase x-phase y‖ ≤ 8*|x-y| := by
  have h := Complex.norm_le_abs_re_add_abs_im (phase x-phase y)
  simp only [phase, Complex.sub_re, Complex.sub_im] at h
  rw [show -triangle (x-1/4) - -triangle (y-1/4) =
    -(triangle (x-1/4)-triangle (y-1/4)) by ring, abs_neg] at h
  have h₁ := triangle_sub_le x y
  have h₂ := triangle_sub_le (x-1/4) (y-1/4)
  rw [show (x-1/4)-(y-1/4) = x-y by ring] at h₂
  unfold phase
  linarith

lemma phase_lipschitz : LipschitzWith 8 phase := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_ofNat] using phase_norm_sub_le x y

lemma segment_phase_sub_le (a : ℝ) {η : ℝ} (hη : |η| ≤ 1/2) (v w : ℝ) :
    ‖phase (a+η*v)-phase (a+η*w)‖ ≤ 4*|v-w| := by
  have h := phase_norm_sub_le (a+η*v) (a+η*w)
  rw [show (a+η*v)-(a+η*w) = η*(v-w) by ring, abs_mul] at h
  nlinarith [abs_nonneg (v-w)]

lemma centered_quadratic_integral (c η : ℝ) :
    (∫ v in (0 : ℝ)..1, (1/2 - 8*(c+η*(v-1/2))^2)) =
      1/2 - 8*c^2 - (2/3)*η^2 := by
  have heq : (fun v : ℝ => 1/2 - 8*(c+η*(v-1/2))^2) =
      (fun v => (1/2-8*c^2+8*c*η-2*η^2) +
        (-16*c*η+8*η^2)*v + (-8*η^2)*v^2) := by
    funext v; ring
  rw [heq, intervalIntegral.integral_add, intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_id, integral_pow]
    norm_num
    ring
  all_goals apply Continuous.intervalIntegrable; fun_prop

lemma centered_integral_re_lower {c η : ℝ} (hc : |c| ≤ 1/8) (hη : |η| ≤ 1/2) :
    5/24 ≤ (∫ v in (0 : ℝ)..1, phase (c+η*(v-1/2))).re := by
  have hf : Continuous (fun v : ℝ => phase (c+η*(v-1/2))) :=
    phase_continuous.comp (by fun_prop)
  have hq : Continuous (fun v : ℝ => 1/2-8*(c+η*(v-1/2))^2) := by fun_prop
  have h := integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    (hq.intervalIntegrable _ _) ((Complex.continuous_re.comp hf).intervalIntegrable _ _)
    (fun v _ => triangle_quadratic_lower (c+η*(v-1/2)))
  rw [centered_quadratic_integral] at h
  change 1/2-8*c^2-(2/3)*η^2 ≤
    ∫ v in (0:ℝ)..1, Complex.reCLM (phase (c+η*(v-1/2))) at h
  rw [Complex.reCLM.intervalIntegral_comp_comm (hf.intervalIntegrable _ _)] at h
  change 1/2-8*c^2-(2/3)*η^2 ≤
    (∫ v in (0:ℝ)..1, phase (c+η*(v-1/2))).re at h
  have hc2 : c^2 ≤ (1/8 : ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg c) (by norm_num)).2 hc
  have hη2 : η^2 ≤ (1/2 : ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg η) (by norm_num)).2 hη
  nlinarith [sq_abs c, sq_abs η]

/-- The normalized interval average appearing in the dyadic majorant. -/
noncomputable def averagePhase (a η : ℝ) : ℂ :=
  ∫ v in (0 : ℝ)..1, phase (a+η*v)

lemma averagePhase_lower (a : ℝ) {η : ℝ} (hη : |η| ≤ 1/2) :
    (1/8 : ℝ) ≤ ‖averagePhase a η‖ := by
  let q : ℤ := round (4*(a+η/2))
  let c : ℝ := a+η/2-(q : ℝ)/4
  have hc : |c| ≤ 1/8 := by
    have h := abs_sub_round (4*(a+η/2))
    have hc4 : 4*c = 4*(a+η/2)-q := by dsimp [c]; ring
    rw [← hc4, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<4)] at h
    linarith
  have hf : (fun v : ℝ => phase (a+η*v)) =
      (fun v => (-Complex.I)^q * phase (c+η*(v-1/2))) := by
    funext v
    rw [← phase_add_quarters]
    congr 1
    dsimp [c]
    ring
  have hn : ‖averagePhase a η‖ = ‖∫ v in (0:ℝ)..1, phase (c+η*(v-1/2))‖ := by
    unfold averagePhase
    rw [hf, intervalIntegral.integral_const_mul, norm_mul, norm_zpow]
    simp
  rw [hn]
  calc
    (1/8 : ℝ) ≤ 5/24 := by norm_num
    _ ≤ (∫ v in (0:ℝ)..1, phase (c+η*(v-1/2))).re := centered_integral_re_lower hc hη
    _ ≤ _ := Complex.re_le_norm _

lemma averagePhase_upper (a η : ℝ) : ‖averagePhase a η‖ ≤ 1 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (fun v _ => phase_norm_le (a+η*v))
  simpa only [averagePhase, sub_zero, abs_one, mul_one] using h

/-- `I(u)` in equation (majorant-integral), without a restriction on u needed
for its analytic bounds. -/
noncomputable def residueIntegral (d : ℕ) (u η : ℝ) : ℂ :=
  (d : ℂ)⁻¹ * averagePhase (u/d) η

lemma residueIntegral_bounds {d : ℕ} (hd : 0 < d) (u : ℝ) {η : ℝ}
    (hη : |η| ≤ 1/2) :
    1/(8*d : ℝ) ≤ ‖residueIntegral d u η‖ ∧ ‖residueIntegral d u η‖ ≤ 1/d := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hn : ‖residueIntegral d u η‖ = (d : ℝ)⁻¹ * ‖averagePhase (u/d) η‖ := by
    rw [residueIntegral, norm_mul, norm_inv, Complex.norm_natCast]
  rw [hn]
  constructor
  · have h := mul_le_mul_of_nonneg_left (averagePhase_lower (u/d) hη)
      (inv_nonneg.mpr hd'.le)
    simpa only [one_div, mul_inv_rev] using h
  · simpa only [mul_one, one_div] using
      mul_le_mul_of_nonneg_left (averagePhase_upper (u/d) η) (inv_nonneg.mpr hd'.le)

/-- Quantitative rectangle rule with exactly the constant required in
(majorant-integral-bounds). -/
lemma rectangle_error {f : ℝ → ℂ} (hf : Continuous f)
    (hL : ∀ v w, ‖f v-f w‖ ≤ 4*|v-w|) (a : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ‖h • f a - ∫ v in a..a+h, f v‖ ≤ 2*h^2 := by
  have heq : (∫ v in a..a+h, (f a-f v)) = h • f a - ∫ v in a..a+h, f v := by
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _), intervalIntegral.integral_const]
    congr 1
    ring_nf
  rw [← heq]
  calc
    _ ≤ ∫ v in a..a+h, ‖f a-f v‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ ≤ ∫ v in a..a+h, 4*(v-a) := by
      apply intervalIntegral.integral_mono_on (by linarith)
        ((continuous_const.sub hf).norm.intervalIntegrable _ _)
        ((show Continuous (fun v : ℝ => 4*(v-a)) by fun_prop).intervalIntegrable _ _)
      intro v hv
      have h₁ := hL a v
      rw [abs_of_nonpos (by linarith [hv.1] : a-v ≤ 0)] at h₁
      change ‖f a-f v‖ ≤ 4*(v-a)
      linarith
    _ = 2*h^2 := by
      rw [intervalIntegral.integral_const_mul]
      have hir : (∫ v in a..a+h, (v-a)) =
          (∫ v in a..a+h, v) - ∫ _ in a..a+h, a :=
        intervalIntegral.integral_sub (f := fun v : ℝ => v) (g := fun _ => a)
          (continuous_id.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
      rw [hir, integral_id, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring

lemma rectangle_sum_error {f : ℝ → ℂ} (hf : Continuous f)
    (hL : ∀ v w, ‖f v-f w‖ ≤ 4*|v-w|) (a : ℝ) {h : ℝ} (hh : 0 ≤ h) (M : ℕ) :
    ‖h • (∑ i ∈ Finset.range M, f (a+i*h)) - ∫ v in a..a+M*h, f v‖ ≤
      M*(2*h^2) := by
  have hInt₀ := intervalIntegral.sum_integral_adjacent_intervals
    (f := f) (μ := volume) (a := fun i : ℕ => a+(i:ℝ)*h) (n := M)
    (fun i _ => hf.intervalIntegrable _ _)
  have hInt : (∑ i ∈ Finset.range M, ∫ v in (a+(i:ℝ)*h)..(a+((i:ℝ)+1)*h), f v) =
      ∫ v in a..a+M*h, f v := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero] using hInt₀
  rw [← hInt, Finset.smul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range M,
        ‖h • f (a+i*h) - ∫ v in (a+i*h)..(a+(i+1)*h), f v‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range M, (2*h^2) := by
      apply Finset.sum_le_sum
      intro i _
      have hr := rectangle_error hf hL (a+(i:ℝ)*h) hh
      simpa only [show a+(i:ℝ)*h+h = a+((i:ℝ)+1)*h by ring] using hr
    _ = M*(2*h^2) := by simp

lemma integral_endpoint_error {f : ℝ → ℂ} (hf : Continuous f)
    (hb : ∀ v, ‖f v‖ ≤ 1) {a b : ℝ} (ha : 0 ≤ a) (hb₁ : 1 ≤ b) :
    ‖(∫ v in a..b, f v) - ∫ v in (0:ℝ)..1, f v‖ ≤ a+(b-1) := by
  have heq : (∫ v in a..b, f v) - ∫ v in (0:ℝ)..1, f v =
      (∫ v in (1:ℝ)..b, f v) - ∫ v in (0:ℝ)..a, f v := by
    have h₁ := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hf.intervalIntegrable 0 a) (hf.intervalIntegrable a b)
    have h₂ := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hf.intervalIntegrable 0 1) (hf.intervalIntegrable 1 b)
    linear_combination h₁ - h₂
  rw [heq]
  have h₁ := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1:ℝ)) (b := b) (fun v _ => hb v)
  have h₂ := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := a) (fun v _ => hb v)
  rw [one_mul, abs_of_nonneg (sub_nonneg.mpr hb₁)] at h₁
  rw [one_mul, sub_zero, abs_of_nonneg ha] at h₂
  calc
    _ ≤ ‖∫ v in (1:ℝ)..b, f v‖ + ‖∫ v in (0:ℝ)..a, f v‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

lemma rectangle_sum_unit_error {f : ℝ → ℂ} (hf : Continuous f)
    (hL : ∀ v w, ‖f v-f w‖ ≤ 4*|v-w|) (hb : ∀ v, ‖f v‖ ≤ 1)
    {a h : ℝ} (hh₀ : 0 ≤ h) (hh₁ : h ≤ 1) (ha₀ : 0 ≤ a) (ha₁ : a ≤ h)
    (M : ℕ) (hM₀ : 1 ≤ a+M*h) (hM₁ : a+M*h ≤ 1+h) :
    ‖h • (∑ i ∈ Finset.range M, f (a+i*h)) - ∫ v in (0:ℝ)..1, f v‖ ≤ 6*h := by
  have h₁ := rectangle_sum_error hf hL a hh₀ M
  have h₂ := integral_endpoint_error hf hb ha₀ hM₀
  have hsplit : h • (∑ i ∈ Finset.range M, f (a+i*h)) - ∫ v in (0:ℝ)..1, f v =
      (h • (∑ i ∈ Finset.range M, f (a+i*h)) - ∫ v in a..a+M*h, f v) +
      ((∫ v in a..a+M*h, f v) - ∫ v in (0:ℝ)..1, f v) := by abel
  rw [hsplit]
  calc
    _ ≤ ‖h • (∑ i ∈ Finset.range M, f (a+i*h)) - ∫ v in a..a+M*h, f v‖ +
      ‖(∫ v in a..a+M*h, f v) - ∫ v in (0:ℝ)..1, f v‖ := norm_add_le _ _
    _ ≤ M*(2*h^2) + a+(a+M*h-1) := by linarith
    _ ≤ 6*h := by
      have h₃ : (M:ℝ)*h ≤ 1+h := by linarith
      have h₄ := mul_le_mul_of_nonneg_right h₃ hh₀
      nlinarith [mul_nonneg hh₀ (sub_nonneg.mpr hh₁)]

end ExactQuantumFactoring.OrderTrial


end

end OAI
