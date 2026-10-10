import OAI.Analysis.PlanarPacking.Cardinal
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

namespace OAI

namespace SharpPlanar
open Set Filter
open scoped Topology
open scoped BigOperators
lemma logSin_hasDeriv (a r x : ℝ) (hx : Real.sin (a*(x-r)) ≠ 0) :
    HasDerivAt (fun u : ℝ => Real.log (Real.sin (a*(u-r))))
      (a*Real.cos (a*(x-r))/Real.sin (a*(x-r))) x := by
  have hd := (((hasDerivAt_id x).sub_const r).const_mul a).sin.log hx
  simpa only [id_eq, mul_one, mul_comm] using hd

lemma cot_scaled_hasDeriv (a r x : ℝ) (hx : Real.sin (a*(x-r)) ≠ 0) :
    HasDerivAt (fun u : ℝ => a*Real.cos (a*(u-r))/Real.sin (a*(u-r)))
      (-a^2/(Real.sin (a*(x-r)))^2) x := by
  have hp := ((hasDerivAt_id x).sub_const r).const_mul a
  have hd := (hp.cos.const_mul a).div hp.sin hx
  simp only [id_eq, mul_one] at hd
  apply hd.congr_deriv
  congr 1
  nlinarith [sq_nonneg a, Real.sin_sq_add_cos_sq (a*(x-r)),
    congrArg (fun t : ℝ => a^2*t) (Real.sin_sq_add_cos_sq (a*(x-r)))]

lemma logSin_concaveOn {D : Set ℝ} (hD : Convex ℝ D) (a r : ℝ)
    (hs : ∀ x ∈ D, Real.sin (a*(x-r)) ≠ 0) :
    ConcaveOn ℝ D (fun x : ℝ => Real.log (Real.sin (a*(x-r)))) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos hD
    (f' := fun x => a*Real.cos (a*(x-r))/Real.sin (a*(x-r)))
    (f'' := fun x => -a^2/Real.sin (a*(x-r))^2)
  · exact (by fun_prop : Continuous fun x : ℝ => Real.sin (a*(x-r))).continuousOn.log hs
  · intro x hx
    exact (logSin_hasDeriv a r x (hs _ (interior_subset hx))).hasDerivWithinAt
  · intro x hx
    exact (cot_scaled_hasDeriv a r x (hs _ (interior_subset hx))).hasDerivWithinAt
  · intro x hx
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (sq_nonneg _)

lemma sinc_ne_zero {a x : ℝ} (ha : a ≠ 0)
    (hs : x ≠ 0 → Real.sin (a*x) ≠ 0) : Real.sinc (a*x) ≠ 0 := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero (mul_ne_zero ha hx)]
    exact div_ne_zero (hs hx) (mul_ne_zero ha hx)

lemma logSinc_hasDeriv (a x : ℝ) (ha : a ≠ 0) (hx : x ≠ 0)
    (hs : Real.sin (a*x) ≠ 0) :
    HasDerivAt (fun u : ℝ => Real.log (Real.sinc (a*u)))
      (a*Real.cos (a*x)/Real.sin (a*x) - 1/x) x := by
  have hp := (hasDerivAt_id x).const_mul a
  have hd := (hp.sin.div hp (mul_ne_zero ha hx)).log (div_ne_zero hs (mul_ne_zero ha hx))
  have he : (fun u : ℝ => Real.log (Real.sinc (a*u))) =ᶠ[𝓝 x]
      (fun u : ℝ => Real.log (Real.sin (a*u)/(a*u))) := by
    filter_upwards [eventually_ne_nhds hx] with u hu
    rw [Real.sinc_of_ne_zero (mul_ne_zero ha hu)]
  apply HasDerivAt.congr_of_eventuallyEq (f := fun u : ℝ => Real.log (Real.sin (a*u)/(a*u))) _ he
  simp only [Pi.div_apply, id_eq, mul_one] at hd
  apply hd.congr_deriv
  field_simp

lemma logSinc_deriv_hasDeriv (a x : ℝ) (hx : x ≠ 0)
    (hs : Real.sin (a*x) ≠ 0) :
    HasDerivAt (fun u : ℝ => a*Real.cos (a*u)/Real.sin (a*u) - 1/u)
      (1/x^2 - a^2/Real.sin (a*x)^2) x := by
  have hd := (cot_scaled_hasDeriv a 0 x (by simpa using hs)).sub
    ((hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx)
  simp only [id_eq, sub_zero, zero_mul, one_mul, zero_sub] at hd
  apply hd.congr_deriv
  ring


lemma logSinc_concaveOn {D : Set ℝ} (hD : Convex ℝ D) (a : ℝ) (ha : a ≠ 0)
    (h0 : (0 : ℝ) ∉ interior D)
    (hs : ∀ x ∈ D, x ≠ 0 → Real.sin (a*x) ≠ 0) :
    ConcaveOn ℝ D (fun x : ℝ => Real.log (Real.sinc (a*x))) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos hD
    (f' := fun x => a*Real.cos (a*x)/Real.sin (a*x) - 1/x)
    (f'' := fun x => 1/x^2 - a^2/Real.sin (a*x)^2)
  · apply (Real.continuous_sinc.comp (by fun_prop)).continuousOn.log
    exact fun x hx => sinc_ne_zero ha (hs x hx)
  · intro x hx
    have hx0 : x ≠ 0 := fun he => h0 (he ▸ hx)
    exact (logSinc_hasDeriv a x ha hx0 (hs x (interior_subset hx) hx0)).hasDerivWithinAt
  · intro x hx
    have hx0 : x ≠ 0 := fun he => h0 (he ▸ hx)
    exact (logSinc_deriv_hasDeriv a x hx0 (hs x (interior_subset hx) hx0)).hasDerivWithinAt
  · intro x hx
    have hx0 : x ≠ 0 := fun he => h0 (he ▸ hx)
    have hsin : Real.sin (a*x) ≠ 0 := hs x (interior_subset hx) hx0
    apply sub_nonpos.mpr
    apply (div_le_div_iff₀ (sq_pos_of_ne_zero hx0) (sq_pos_of_ne_zero hsin)).mpr
    have hh : Real.sin (a*x)^2 ≤ (a*x)^2 := by
      exact sq_le_sq.mpr Real.abs_sin_le_abs
    nlinarith

end SharpPlanar


namespace SharpPlanar
open Set Filter
open scoped Topology

noncomputable def dividedP (a : ℕ) (u : ℝ) : ℝ :=
  (Real.pi/6)^2 * (Real.sinc (Real.pi*u/12))^2 *
    ∏ r ∈ residues.erase a, (2*Real.sin (Real.pi*(a+u-r)/12))^2

lemma dividedP_zero (a : ℕ) (ha : a < 12) : dividedP a 0 = Q a := by
  simp [dividedP,Q,Nat.mod_eq_of_lt ha]

lemma dividedP_factor (a : ℕ) (ha : a ∈ residues) (u : ℝ) :
    u^2 * dividedP a u = P (a+u) := by
  rw [P,← Finset.mul_prod_erase residues (fun r : ℕ => (2*Real.sin (Real.pi*(a+u-r)/12))^2) ha]
  unfold dividedP
  rw [show ((a:ℝ)+u-a)=u by ring]
  have hs : (Real.pi*u/12)*Real.sinc (Real.pi*u/12) = Real.sin (Real.pi*u/12) := by
    by_cases hz : Real.pi*u/12 = 0
    · simp [hz]
    · rw [Real.sinc_of_ne_zero hz,mul_div_cancel₀ _ hz]
  rw [← hs]
  ring

lemma sine_twelfth_ne {v : ℝ} (hl : -12 < v) (hr : v < 12) (hv : v ≠ 0) :
    Real.sin (Real.pi*v/12) ≠ 0 := by
  rw [ne_eq,Real.sin_eq_zero_iff_of_lt_of_lt
    (by nlinarith [Real.pi_pos,mul_pos Real.pi_pos (show 0 < v+12 by linarith)])
    (by nlinarith [Real.pi_pos,mul_pos Real.pi_pos (show 0 < 12-v by linarith)])]
  exact div_ne_zero (mul_ne_zero Real.pi_ne_zero hv) (by norm_num)

noncomputable def leftHalf : ℕ → ℝ
  | 0 => 3/2 | 1 => 1/2 | 3 => 1 | 4 => 1/2 | 7 => 3/2 | 9 => 1 | _ => 0
noncomputable def rightHalf : ℕ → ℝ
  | 0 => 1/2 | 1 => 1 | 3 => 1/2 | 4 => 3/2 | 7 => 1 | 9 => 3/2 | _ => 0

lemma half_pos (a : ℕ) (ha : a ∈ residues) : 0 < leftHalf a ∧ 0 < rightHalf a := by
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [leftHalf,rightHalf]
lemma half_bounds (a : ℕ) (ha : a ∈ residues) {u : ℝ}
    (hu : u ∈ Icc (-leftHalf a) (rightHalf a)) : -12 < u ∧ u < 12 := by
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [leftHalf,rightHalf,mem_Icc] at hu <;>
    constructor <;> linarith
lemma other_sine_ne (a : ℕ) (ha : a ∈ residues) {u : ℝ}
    (hu : u ∈ Icc (-leftHalf a) (rightHalf a)) (r : ℕ) (hr : r ∈ residues.erase a) :
    Real.sin (Real.pi*(a+u-r)/12) ≠ 0 := by
  apply sine_twelfth_ne
  all_goals
    have hra := (Finset.mem_erase.mp hr).1
    have hrr := (Finset.mem_erase.mp hr).2
    simp only [residues,Finset.mem_insert,Finset.mem_singleton] at ha hrr
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl <;>
      rcases hrr with rfl|rfl|rfl|rfl|rfl|rfl <;>
      first | contradiction | (norm_num [leftHalf,rightHalf,mem_Icc] at hu ⊢; grind)

lemma dividedP_pos (a : ℕ) (ha : a ∈ residues) {u : ℝ}
    (hu : u ∈ Icc (-leftHalf a) (rightHalf a)) : 0 < dividedP a u := by
  apply mul_pos
  · apply mul_pos (sq_pos_of_pos (by positivity))
    apply sq_pos_of_ne_zero
    rw [show Real.pi*u/12=(Real.pi/12)*u by ring]
    apply sinc_ne_zero (a := Real.pi/12) (by positivity)
    intro hu0
    have hb := half_bounds a ha hu
    convert sine_twelfth_ne hb.1 hb.2 hu0 using 1; congr 1; ring
  · exact Finset.prod_pos (fun r hr => sq_pos_of_ne_zero (mul_ne_zero (by norm_num) (other_sine_ne a ha hu r hr)))

lemma dividedP_log (a : ℕ) (ha : a ∈ residues) {u : ℝ}
    (hu : u ∈ Icc (-leftHalf a) (rightHalf a)) :
    Real.log (dividedP a u) = 2*Real.log (Real.pi/6) +
      2*Real.log (Real.sinc (Real.pi*u/12)) +
      ∑ r ∈ residues.erase a, (2*Real.log 2 + 2*Real.log (Real.sin (Real.pi*(a+u-r)/12))) := by
  have hn (r : ℕ) (hr : r ∈ residues.erase a) : 2*Real.sin (Real.pi*(a+u-r)/12) ≠ 0 :=
    mul_ne_zero (by norm_num) (other_sine_ne a ha hu r hr)
  have hb := half_bounds a ha hu
  have hsi : Real.sinc (Real.pi*u/12) ≠ 0 := by
    convert sinc_ne_zero (a := Real.pi/12) (by positivity)
      (fun hu0 => by convert sine_twelfth_ne hb.1 hb.2 hu0 using 1; congr 1; ring) using 1; congr 1; ring
  unfold dividedP
  rw [Real.log_mul (mul_ne_zero (pow_ne_zero 2 (by positivity)) (pow_ne_zero 2 hsi)) (Finset.prod_ne_zero_iff.mpr (fun r hr => pow_ne_zero 2 (hn r hr))),
    Real.log_mul (pow_ne_zero 2 (by positivity)) (pow_ne_zero 2 hsi),Real.log_pow,Real.log_pow,Real.log_prod (fun r hr => pow_ne_zero 2 (hn r hr))]
  simp only [Nat.cast_ofNat]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [Real.log_pow,Real.log_mul (by norm_num) (other_sine_ne a ha hu r hr)]
  push_cast
  ring

end SharpPlanar


namespace SharpPlanar
open Set Filter
open scoped Topology

lemma concaveOn_finset_sum {ι : Type*} (s : Finset ι) {D : Set ℝ}
    (hD : Convex ℝ D) (g : ι → ℝ → ℝ) (hg : ∀ r ∈ s, ConcaveOn ℝ D (g r)) :
    ConcaveOn ℝ D (fun u => ∑ r ∈ s, g r u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using concaveOn_const (0:ℝ) hD
  | @insert r s hrs ih =>
    have hh : ConcaveOn ℝ D (fun u => g r u + ∑ r ∈ s, g r u) := (hg r (Finset.mem_insert_self ..)).add (ih (fun v hv => hg v (Finset.mem_insert_of_mem hv)))
    simpa only [Finset.sum_insert hrs, Pi.add_apply] using hh

lemma dividedP_log_concave (a : ℕ) (ha : a ∈ residues) {D : Set ℝ}
    (hD : Convex ℝ D) (hsub : D ⊆ Icc (-leftHalf a) (rightHalf a))
    (h0 : (0:ℝ) ∉ interior D) : ConcaveOn ℝ D (fun u => Real.log (dividedP a u)) := by
  have hsinc0 := logSinc_concaveOn hD (Real.pi/12) (by positivity) h0 (fun u hu hu0 => by
    have hb := half_bounds a ha (hsub hu)
    rw [show (Real.pi/12)*u = Real.pi*u/12 by ring]
    exact sine_twelfth_ne hb.1 hb.2 hu0)
  have hsinc : ConcaveOn ℝ D (fun u => Real.log (Real.sinc (Real.pi*u/12))) := by
    apply hsinc0.congr
    intro u hu
    dsimp only
    rw [show (Real.pi/12)*u = Real.pi*u/12 by ring]
  have hother (r : ℕ) (hr : r ∈ residues.erase a) :
      ConcaveOn ℝ D (fun u => 2*Real.log 2 + 2*Real.log (Real.sin (Real.pi*(a+u-r)/12))) := by
    have hh0 := logSin_concaveOn hD (Real.pi/12) ((r:ℝ)-a) (fun u hu => by
      rw [show (Real.pi/12)*(u-((r:ℝ)-a)) = Real.pi*(a+u-r)/12 by ring]
      exact other_sine_ne a ha (hsub hu) r hr)
    have hh : ConcaveOn ℝ D (fun u => Real.log (Real.sin (Real.pi*(a+u-r)/12))) := by
      apply hh0.congr
      intro u hu
      dsimp only
      rw [show (Real.pi/12)*(u-((r:ℝ)-a)) = Real.pi*(a+u-r)/12 by ring]
    exact (concaveOn_const (2*Real.log 2) hD).add (ConcaveOn.smul (by norm_num : 0 ≤ (2:ℝ)) hh)
  have hh : ConcaveOn ℝ D (fun u => 2*Real.log (Real.pi/6) + 2*Real.log (Real.sinc (Real.pi*u/12)) + ∑ r ∈ residues.erase a, (2*Real.log 2 + 2*Real.log (Real.sin (Real.pi*(a+u-r)/12)))) := ((concaveOn_const (2*Real.log (Real.pi/6)) hD).add
    (ConcaveOn.smul (by norm_num : 0 ≤ (2:ℝ)) hsinc)).add
      (concaveOn_finset_sum (residues.erase a) hD _ hother)
  apply hh.congr
  intro u hu
  exact (dividedP_log a ha (hsub hu)).symm

lemma lower_of_log_concave {f : ℝ → ℝ} {v w l : ℝ} (hl : 0 < l)
    (hp : ∀ u ∈ uIcc v w, 0 < f u)
    (hc : ConcaveOn ℝ (uIcc v w) (fun u => Real.log (f u)))
    (hv : l ≤ f v) (hw : l ≤ f w) {u : ℝ} (hu : u ∈ uIcc v w) : l ≤ f u := by
  have hs := hc.ge_on_segment (left_mem_uIcc) (right_mem_uIcc)
    (show u ∈ segment ℝ v w by simpa only [segment_eq_uIcc] using hu)
  have hj : Real.log l ≤ Real.log (f u) := le_trans (le_min
    (Real.log_le_log hl hv) (Real.log_le_log hl hw)) hs
  exact (Real.log_le_log_iff hl (hp u hu)).mp hj

end SharpPlanar

end OAI
