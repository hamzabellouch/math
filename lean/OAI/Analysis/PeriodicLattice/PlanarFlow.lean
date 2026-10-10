import OAI.Analysis.PeriodicLattice.Planar
import OAI.Analysis.PeriodicLattice.Trajectories

namespace OAI

/-! Planar trajectories, support control and dynamical identities. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingPlanarFlow {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace Planar

open Profiles Scales
open scoped ContDiff

def codes (F : ℕ → ℤ → ℕ) (c₀ : ℕ) : ℕ → ℕ
  | 0 => c₀
  | n + 1 => F n (codes F c₀ n)

theorem codes_bound {b : ℕ} (L c₀ : ℕ) (F : ℕ → ℤ → ℕ)
    (hc₀ : c₀ < capacity b L 0)
    (hF : ∀ n j, F n j < capacity b L (n + 1)) :
    ∀ n, codes F c₀ n < capacity b L n := by
  intro n
  cases n with
  | zero => exact hc₀
  | succ n => exact hF n _

theorem table_residue {A : Type*} (V : ℤ → A) (P : ℤ)
    (hV : Function.Periodic V P) (j : ℤ) : V j = V (j % P) := by
  have h := hV.int_mul (j / P) (j % P)
  rw [Int.cast_id, mul_comm, Int.emod_add_mul_ediv] at h
  exact h

theorem table_history {A : Type*} (V : ℤ → A) (b L : ℕ) (c : ℕ → ℕ) (n : ℕ)
    (hV : Function.Periodic V (capacity b L n : ℤ)) (hc : c n < capacity b L n) :
    V (History.address b L c n) = V (c n) := by
  rw [table_residue V _ hV]
  congr 1
  exact_mod_cast History.read_residue b L c n hc

def increments (b L : ℕ) (c : ℕ → ℕ) (H : ℕ → ℤ → Bool) : ℕ → Point
  | 0 => (0, epsilon b L 0 * c 0)
  | n + 1 =>
    (beta b L n - beta b L (n + 1) +
        2 * beta b L (n + 1) * (if H n (c n) then 1 else 0),
      epsilon b L (n + 1) * c (n + 1))

def curve (b L : ℕ) (c : ℕ → ℕ) (H : ℕ → ℤ → Bool) (t : ℝ) : Point :=
  (1 / 4, 1 / 2) + accumulated (increments b L c H) t

theorem curve_contDiff (b L : ℕ) (c : ℕ → ℕ) (H : ℕ → ℤ → Bool) :
    ContDiff ℝ ∞ (curve b L c H) := contDiff_const.add (accumulated_contDiff _)

theorem curve_start (b L : ℕ) (c : ℕ → ℕ) (H : ℕ → ℤ → Bool) :
    curve b L c H 0 = (1 / 4, 1 / 2) := by
  have ha := accumulated_at_integer (increments b L c H) 0
  simpa only [Nat.cast_zero, Finset.sum_range_zero, curve, add_eq_left] using ha

theorem curve_succ (b L : ℕ) (c : ℕ → ℕ) (H : ℕ → ℤ → Bool) (n : ℕ) :
    curve b L c H (n + 1) = curve b L c H n + increments b L c H n := by
  have hn : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by push_cast; rfl
  rw [hn, curve, accumulated_at_integer, Finset.sum_range_succ]
  rw [curve, accumulated_at_integer, add_assoc]

theorem curve_on_slot (b L : ℕ) (c : ℕ → ℕ) (H : ℕ → ℤ → Bool) (n : ℕ)
    {t : ℝ} (ht : (n : ℝ) ≤ t) (ht' : t ≤ n + 1) :
    curve b L c H t = curve b L c H n + shiftedClock n t • increments b L c H n := by
  rw [curve, accumulated_on_slot _ n ht ht', curve, accumulated_at_integer, add_assoc]

theorem curve_y_integer (b L : ℕ) (c : ℕ → ℕ) (H : ℕ → ℤ → Bool) (n : ℕ) :
    (curve b L c H (n + 1)).2 = History.coordinate b L c n := by
  induction n with
  | zero =>
    have he := congrArg Prod.snd (curve_succ b L c H 0)
    simpa [curve_start, increments, History.coordinate] using he
  | succ n ih =>
    have he := congrArg Prod.snd (curve_succ b L c H (n + 1))
    simp only [Prod.snd_add, Nat.cast_add, Nat.cast_one, increments] at he
    rw [Nat.cast_add, Nat.cast_one, he, ih]
    change (1 / 2 + ∑ k ∈ Finset.range (n + 1), epsilon b L k * (c k : ℝ)) +
      epsilon b L (n + 1) * c (n + 1) =
      1 / 2 + ∑ k ∈ Finset.range ((n + 1) + 1), epsilon b L k * (c k : ℝ)
    rw [Finset.sum_range_succ _ (n + 1), add_assoc]

theorem curve_y_slot (b L : ℕ) (c : ℕ → ℕ) (H : ℕ → ℤ → Bool) (n : ℕ)
    {t : ℝ} (ht : (n : ℝ) + 1 ≤ t) (ht' : t ≤ n + 2) :
    (curve b L c H t).2 = History.coordinate b L c n +
      clock (t - 1 - n) * (epsilon b L (n + 1) * c (n + 1)) := by
  rw [curve_on_slot _ _ _ _ (n + 1) (by push_cast; exact ht) (by push_cast; linarith)]
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, Nat.cast_add, Nat.cast_one,
    curve_y_integer, shiftedClock, increments, sub_add_eq_sub_sub, sub_right_comm]

theorem curve_plateau {b : ℕ} (hb : 2 ≤ b) (L : ℕ) (c : ℕ → ℕ)
    (H : ℕ → ℤ → Bool) (n : ℕ) (hc : c (n + 1) < capacity b L (n + 1))
    {t : ℝ} (ht : (n : ℝ) + 1 ≤ t) (ht' : t ≤ n + 2) :
    |((curve b L c H t).2 - 1 / 2) / epsilon b L n -
      (History.address b L c n : ℝ)| ≤ 1 / 4 := by
  rw [curve_y_slot b L c H n ht ht']
  simpa only [mul_assoc] using
    (Signal.history_in_plateau hb L n c hc (clock_nonneg (t - 1 - n)) (clock_le_one _)).le

end Planar

namespace Planar

open Profiles Scales
open scoped ContDiff

def ruleField (b L c₀ : ℕ) (F : ℕ → ℤ → ℕ) (H : ℕ → ℤ → Bool) : ℝ → Point → Point :=
  field b L c₀ (fun n j => F n j) (fun n j => if H n j then 1 else 0)

theorem coefficients_on_curve {b : ℕ} (hb : 2 ≤ b) (L : ℕ) (F : ℕ → ℤ → ℕ)
    (H : ℕ → ℤ → Bool) (c : ℕ → ℕ)
    (hc : ∀ n, c n < capacity b L n)
    (hstep : ∀ n, c (n + 1) = F n (c n))
    (hF : ∀ n, Function.Periodic (F n) (capacity b L n : ℤ))
    (hH : ∀ n, Function.Periodic (H n) (capacity b L n : ℤ))
    (n : ℕ) {t : ℝ} (ht : (n : ℝ) ≤ t) (ht' : t ≤ n + 1) :
    coefficients b L (c 0) (fun m j => F m j) (fun m j => if H m j then 1 else 0)
      n (curve b L c H t).2 = increments b L c H n := by
  cases n with
  | zero => rfl
  | succ n =>
    have hl : (n : ℝ) + 1 ≤ t := by simpa using ht
    have hu : t ≤ (n : ℝ) + 2 := by push_cast at ht'; linarith
    have hp : |((curve b L c H t).2 - 1 / 2) / epsilon b L n -
        ((History.address b L c n : ℤ) : ℝ)| ≤ 1 / 4 := by
      simpa using curve_plateau hb L c H n (hc (n + 1)) hl hu
    dsimp only [coefficients, slot, increments]
    rw [selector_plateau _ _ hp, selector_plateau _ _ hp,
      table_history (H n) b L c n (hH n) (hc n),
      table_history (F n) b L c n (hF n) (hc n), ← hstep n]

theorem curve_solves {b : ℕ} (hb : 2 ≤ b) (L c₀ : ℕ) (F : ℕ → ℤ → ℕ)
    (H : ℕ → ℤ → Bool) (hc₀ : c₀ < capacity b L 0)
    (hbound : ∀ n j, F n j < capacity b L (n + 1))
    (hF : ∀ n, Function.Periodic (F n) (capacity b L n : ℤ))
    (hH : ∀ n, Function.Periodic (H n) (capacity b L n : ℤ))
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (curve b L (codes F c₀) H)
      (ruleField b L c₀ F H t (curve b L (codes F c₀) H t)) t := by
  let n : ℕ := ⌊t⌋₊
  have hl : (n : ℝ) ≤ t := Nat.floor_le ht
  have hu : t ≤ n + 1 := (Nat.lt_floor_add_one t).le
  have hc := codes_bound L c₀ F hc₀ hbound
  have heq : ruleField b L c₀ F H t (curve b L (codes F c₀) H t) =
      pulse n t • increments b L (codes F c₀) H n := by
    rw [ruleField, field, schedule_on_slot _ n hl hu]
    congr 1
    exact coefficients_on_curve hb L F H (codes F c₀) hc (fun _ => rfl) hF hH n hl hu
  rw [heq]
  exact (accumulated_hasDerivAt (increments b L (codes F c₀) H) n hl hu).const_add (1 / 4, 1 / 2)

theorem curve_unique {b : ℕ} (hb : 2 ≤ b) (L c₀ : ℕ) (F : ℕ → ℤ → ℕ)
    (H : ℕ → ℤ → Bool) (hc₀ : c₀ < capacity b L 0)
    (hbound : ∀ n j, F n j < capacity b L (n + 1))
    (hF : ∀ n, Function.Periodic (F n) (capacity b L n : ℤ))
    (hH : ∀ n, Function.Periodic (H n) (capacity b L n : ℤ))
    {Y : ℝ → Point} (hY₀ : Y 0 = (1 / 4, 1 / 2))
    (hY : ∀ t : ℝ, 0 ≤ t →
      HasDerivWithinAt Y (ruleField b L c₀ F H t (Y t)) (Set.Ici 0) t)
    {t : ℝ} (ht : 0 ≤ t) : Y t = curve b L (codes F c₀) H t := by
  apply Trajectories.unique
    ((field_contDiff b L c₀ (fun n j => F n j) (fun n j => if H n j then 1 else 0)).of_le
      (by exact WithTop.coe_le_coe.mpr le_top)) hY
    (fun s hs => (curve_solves hb L c₀ F H hc₀ hbound hF hH hs).hasDerivWithinAt) _ ht
  rw [hY₀, curve_start]

end Planar

namespace Planar

open Profiles Scales

theorem curve_x_before (b L : ℕ) (c : ℕ → ℕ) (H : ℕ → ℤ → Bool) (n : ℕ)
    (hH : ∀ m < n, H m (c m) = false) :
    (curve b L c H (n + 1)).1 = 1 / 2 - beta b L n := by
  induction n with
  | zero =>
    have he := congrArg Prod.fst (curve_succ b L c H 0)
    norm_num [curve_start, increments, beta] at he ⊢
    exact he
  | succ n ih =>
    have hn : H n (c n) = false := hH n (Nat.lt_succ_self n)
    have hi := ih (fun m hm => hH m (Nat.lt_succ_of_lt hm))
    have he := congrArg Prod.fst (curve_succ b L c H (n + 1))
    simp only [Prod.fst_add, Nat.cast_add, Nat.cast_one, increments, hn,
      Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero] at he
    rw [Nat.cast_add, Nat.cast_one, he, hi]
    ring

theorem curve_x_loader (b L : ℕ) (c : ℕ → ℕ) (H : ℕ → ℤ → Bool) {t : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1) : (curve b L c H t).1 = 1 / 4 := by
  rw [curve_on_slot b L c H 0 (by simpa using ht) (by simpa using ht')]
  simp [curve_start, increments]

theorem curve_x_slot (b L : ℕ) (c : ℕ → ℕ) (H : ℕ → ℤ → Bool) (n : ℕ)
    (hH : ∀ m < n, H m (c m) = false)
    {t : ℝ} (ht : (n : ℝ) + 1 ≤ t) (ht' : t ≤ n + 2) :
    (curve b L c H t).1 = Signal.inSlot b L n (H n (c n)) (clock (t - 1 - n)) := by
  rw [curve_on_slot b L c H (n + 1) (by push_cast; exact ht) (by push_cast; linarith)]
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, Nat.cast_add, Nat.cast_one,
    curve_x_before b L c H n hH, increments, shiftedClock, Signal.inSlot,
    sub_add_eq_sub_sub, sub_right_comm]
  cases H n (c n) <;> simp

theorem curve_no_signal {b : ℕ} (hb : 2 ≤ b) (L : ℕ) (c : ℕ → ℕ)
    (H : ℕ → ℤ → Bool) (hH : ∀ n, H n (c n) = false) {t : ℝ} (ht : 0 ≤ t) :
    1 / 4 ≤ (curve b L c H t).1 ∧ (curve b L c H t).1 < 1 / 2 := by
  by_cases ht' : t ≤ 1
  · rw [curve_x_loader b L c H ht ht']
    norm_num
  · let n : ℕ := ⌊t - 1⌋₊
    have hl : (n : ℝ) + 1 ≤ t := by
      have := Nat.floor_le (show 0 ≤ t - 1 by linarith)
      dsimp [n]; linarith
    have hu : t ≤ (n : ℝ) + 2 := by
      have := Nat.lt_floor_add_one (t - 1)
      dsimp [n]; linarith
    rw [curve_x_slot b L c H n (fun m _ => hH m) hl hu, hH]
    exact (Signal.nonhalting_interval hb L n (clock_nonneg _) (clock_le_one _)).2.2

theorem curve_first_signal {b : ℕ} (hb : 2 ≤ b) (L : ℕ) (c : ℕ → ℕ)
    (H : ℕ → ℤ → Bool) (n : ℕ) (hbefore : ∀ m < n, H m (c m) = false)
    (hn : H n (c n) = true) :
    1 / 2 < (curve b L c H (n + 2)).1 ∧ (curve b L c H (n + 2)).1 < 1 := by
  rw [curve_x_slot b L c H n hbefore (by linarith) le_rfl, hn,
    clock_one (by linarith)]
  exact Signal.halting_interval hb L n

def embed (x : Point) : Space := WithLp.toLp 2 ![x.1, x.2, 1 / 2]

@[simp] theorem embed_first (x : Point) : embed x 0 = x.1 := rfl

theorem curve_event_iff {b : ℕ} (hb : 2 ≤ b) (L : ℕ) (c : ℕ → ℕ)
    (H : ℕ → ℤ → Bool) :
    MaterialEvent (fun t => embed (curve b L c H t)) ↔ ∃ n : ℕ, H n (c n) = true := by
  constructor
  · rintro ⟨t, ht, hevent⟩
    by_contra hn
    have hh : ∀ n, H n (c n) = false := by
      intro n
      exact Bool.eq_false_iff.mpr (fun h => hn ⟨n, h⟩)
    obtain ⟨hlo, hhi⟩ := curve_no_signal hb L c H hh ht
    have hlo' : 0 ≤ embed (curve b L c H t) 0 := by simp only [embed_first]; linarith
    have hhi' : embed (curve b L c H t) 0 < 1 := by simp only [embed_first]; linarith
    have := (Detector.mem_iff hlo' hhi').mp hevent
    exact (not_lt_of_ge hhi.le) this
  · intro hn
    let n := Nat.find hn
    have hsig : H n (c n) = true := Nat.find_spec hn
    have hbefore : ∀ m < n, H m (c m) = false := by
      intro m hm
      exact Bool.eq_false_iff.mpr (Nat.find_min hn hm)
    obtain ⟨hlo, hhi⟩ := curve_first_signal hb L c H n hbefore hsig
    refine ⟨(n : ℝ) + 2, by positivity, ?_⟩
    apply (Detector.mem_iff (x := embed (curve b L c H (n + 2))) ?_ ?_).mpr
    · exact hlo
    · simp only [embed_first]; linarith
    · exact hhi

end Planar

namespace Profiles

open scoped ContDiff

theorem iteratedDeriv_pair {a d : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hd : ContDiff ℝ ∞ d)
    (k : ℕ) : iteratedDeriv k (fun y => (a y, d y)) =
      fun y => (iteratedDeriv k a y, iteratedDeriv k d y) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    have ha' : DifferentiableAt ℝ (iteratedDeriv k a) y := by
      rw [iteratedDeriv_eq_iterate]
      exact (ContDiff.iterate_deriv k ha).differentiable (by norm_num) y
    have hd' : DifferentiableAt ℝ (iteratedDeriv k d) y := by
      rw [iteratedDeriv_eq_iterate]
      exact (ContDiff.iterate_deriv k hd).differentiable (by norm_num) y
    simpa only [iteratedDeriv_succ] using (ha'.hasDerivAt.prodMk hd'.hasDerivAt).deriv

end Profiles

namespace Planar

open Profiles Scales
open scoped ContDiff

theorem slot_iteratedDeriv (b L n k : ℕ) (F H : ℤ → ℝ) (y : ℝ) :
    iteratedDeriv k (slot b L n F H) y =
      ((if k = 0 then beta b L n - beta b L (n + 1) else 0) +
          2 * beta b L (n + 1) * iteratedDeriv k (selector (epsilon b L n) H) y,
        epsilon b L (n + 1) * iteratedDeriv k (selector (epsilon b L n) F) y) := by
  have hh : ContDiff ℝ ∞ (fun y => beta b L n - beta b L (n + 1) +
      2 * beta b L (n + 1) * selector (epsilon b L n) H y) :=
    contDiff_const.add (contDiff_const.mul (selector_contDiff _ _))
  have hf : ContDiff ℝ ∞ (fun y => epsilon b L (n + 1) * selector (epsilon b L n) F y) :=
    contDiff_const.mul (selector_contDiff _ _)
  unfold slot
  rw [iteratedDeriv_pair hh hf]
  dsimp only
  apply Prod.ext
  · rw [iteratedDeriv_fun_add contDiffAt_const
      ((contDiff_const.mul (selector_contDiff _ _)).of_le
        (WithTop.coe_le_coe.mpr le_top)).contDiffAt, iteratedDeriv_const,
        iteratedDeriv_const_mul_field]
  · rw [iteratedDeriv_const_mul_field]

theorem slot_derivative_bound {b : ℕ} (hb : 2 ≤ b) (L n k : ℕ) (F H : ℤ → ℝ)
    {D : ℝ} (hF : ∀ j, |F j| ≤ (capacity b L (n + 1) : ℝ))
    (hH : ∀ j, |H j| ≤ 1) (hD : ∀ z, |iteratedDeriv k bump z| ≤ D) (y : ℝ) :
    ‖iteratedDeriv k (slot b L n F H) y‖ ≤ (1 + 2 * D) * slotSize b L k n := by
  have he := epsilon_pos hb L n
  have he' := epsilon_pos hb L (n + 1)
  have hD₀ : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hP : (1 : ℝ) ≤ capacity b L (n + 1) := by
    exact_mod_cast Nat.one_le_pow (codeExponent L (n + 1)) b (by omega)
  have hdH := selector_derivative_bound he H k hH hD y
  have hdF := selector_derivative_bound he F k hF hD y
  simp only [one_mul] at hdH
  let E : ℝ := (capacity b L (n + 1) : ℝ) * epsilon b L (n + 1) / epsilon b L n ^ k
  have hE : E = (capacity b L (n + 1) : ℝ) * epsilon b L (n + 1) *
      (epsilon b L n)⁻¹ ^ k := by simp only [E, div_eq_mul_inv, inv_pow]
  have hE₀ : 0 ≤ E := by dsimp [E]; positivity
  have hE' : epsilon b L (n + 1) * (epsilon b L n)⁻¹ ^ k ≤ E := by
    rw [hE]
    have hh := mul_le_mul_of_nonneg_right hP
      (show 0 ≤ epsilon b L (n + 1) * (epsilon b L n)⁻¹ ^ k by positivity)
    simpa only [one_mul, mul_assoc] using hh
  let A : ℝ := if k = 0 then beta b L n else 0
  have hA₀ : 0 ≤ A := by
    dsimp [A]
    split_ifs
    · exact (beta_pos hb L n).le
    · exact le_rfl
  have hconst : |if k = 0 then beta b L n - beta b L (n + 1) else 0| ≤ A := by
    dsimp [A]
    split_ifs
    · rw [abs_of_nonneg (sub_nonneg.mpr ((beta_strictAnti hb L).antitone (Nat.le_succ n)))]
      linarith [beta_pos hb L (n + 1)]
    · simp
  have hbeta : beta b L (n + 1) = epsilon b L (n + 1) := by simp [beta]
  rw [slot_iteratedDeriv, norm_prod_le_iff]
  change _ ≤ (1 + 2 * D) * (A + E) ∧ _ ≤ (1 + 2 * D) * (A + E)
  constructor
  · rw [Real.norm_eq_abs]
    calc
      _ ≤ |if k = 0 then beta b L n - beta b L (n + 1) else 0| +
          |2 * beta b L (n + 1) * iteratedDeriv k (selector (epsilon b L n) H) y| :=
        abs_add_le _ _
      _ ≤ A + 2 * epsilon b L (n + 1) * ((epsilon b L n)⁻¹ ^ k * D) := by
        rw [abs_mul, hbeta, abs_of_nonneg (by positivity : 0 ≤ 2 * epsilon b L (n + 1))]
        exact add_le_add hconst (mul_le_mul_of_nonneg_left hdH (by positivity))
      _ ≤ A + 2 * D * E := by nlinarith [mul_le_mul_of_nonneg_left hE' hD₀]
      _ ≤ (1 + 2 * D) * (A + E) := by nlinarith
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos he']
    calc
      _ ≤ epsilon b L (n + 1) *
          ((capacity b L (n + 1) : ℝ) * (epsilon b L n)⁻¹ ^ k * D) :=
        mul_le_mul_of_nonneg_left hdF he'.le
      _ = D * E := by rw [hE]; ring
      _ ≤ (1 + 2 * D) * (A + E) := by nlinarith

end Planar

namespace Planar

open Profiles Scales
open scoped ContDiff

theorem field_slot_derivative_bound {b : ℕ} (hb : 2 ≤ b) (L c₀ r k n : ℕ)
    (F H : ℕ → ℤ → ℝ) {T D : ℝ}
    (hF : ∀ m j, |F m j| ≤ (capacity b L (m + 1) : ℝ))
    (hH : ∀ m j, |H m j| ≤ 1)
    (hT : ∀ s, |iteratedDeriv r (deriv clock) s| ≤ T)
    (hD : ∀ z, |iteratedDeriv k bump z| ≤ D)
    {t : ℝ} (ht : (n : ℝ) + 1 ≤ t) (ht' : t ≤ n + 2) (y : ℝ) :
    ‖mixedPartial r k (schedule (coefficients b L c₀ F H)) t y‖ ≤
      T * (1 + 2 * D) * slotSize b L k n := by
  rw [schedule_mixedPartial _ r k (n + 1) (by push_cast; exact ht) (by push_cast; linarith),
    norm_smul, Real.norm_eq_abs, pulse_iteratedDeriv]
  have h := slot_derivative_bound hb L n k (F n) (H n) (hF n) (hH n) hD y
  have hT₀ : 0 ≤ T := (abs_nonneg _).trans (hT 0)
  have hbound := mul_le_mul (hT (t - (n + 1 : ℕ))) h (norm_nonneg _) hT₀
  simpa only [coefficients, mul_assoc] using hbound

def planarBound (b L c₀ k J T D : ℕ) : ℕ :=
  T * ((1 + 2 * D) * allSlotsBound b L k J + c₀ * 2 ^ J)

theorem field_weighted_derivative_bound {b : ℕ} (hb : 2 ≤ b) (L c₀ r k J T D : ℕ)
    (F H : ℕ → ℤ → ℝ)
    (hF : ∀ m j, |F m j| ≤ (capacity b L (m + 1) : ℝ))
    (hH : ∀ m j, |H m j| ≤ 1)
    (hT : ∀ s, |iteratedDeriv r (deriv clock) s| ≤ T)
    (hD : ∀ z, |iteratedDeriv k bump z| ≤ D)
    {t : ℝ} (ht : 0 ≤ t) (y : ℝ) :
    (1 + t) ^ J * ‖mixedPartial r k (schedule (coefficients b L c₀ F H)) t y‖ ≤
      (planarBound b L c₀ k J T D : ℝ) := by
  have hweight : 0 ≤ (1 + t) ^ J := by positivity
  have hbudget : ((T : ℝ) * (1 + 2 * D) * allSlotsBound b L k J) ≤
      (planarBound b L c₀ k J T D : ℝ) := by
    simp only [planarBound, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_pow]
    nlinarith [show 0 ≤ (T : ℝ) * (c₀ * 2 ^ J) by positivity]
  by_cases ht' : t ≤ 1
  · rw [schedule_mixedPartial _ r k 0 (by simpa using ht) (by simpa using ht')]
    dsimp only [coefficients]
    rw [Nat.rec_zero, iteratedDeriv_const, norm_smul, Real.norm_eq_abs, pulse_iteratedDeriv]
    have hloader : ‖if k = 0 then ((0 : ℝ), epsilon b L 0 * c₀) else 0‖ ≤ (c₀ : ℝ) := by
      split_ifs
      · rw [norm_prod_le_iff]
        constructor
        · simp
        · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (epsilon_pos hb L 0).le (Nat.cast_nonneg c₀))]
          simpa using mul_le_mul_of_nonneg_right (epsilon_le_one hb L 0) (Nat.cast_nonneg c₀)
      · simp
    have hpulse : |iteratedDeriv r (deriv clock) (t - (0 : ℕ))| ≤ (T : ℝ) := hT _
    have hw : (1 + t) ^ J ≤ (2 : ℝ) ^ J :=
      pow_le_pow_left₀ (by linarith) (by linarith) J
    calc
      _ ≤ (2 : ℝ) ^ J * ((T : ℝ) * c₀) :=
        mul_le_mul hw (mul_le_mul hpulse hloader (norm_nonneg _) (Nat.cast_nonneg T))
          (by positivity) (by positivity)
      _ ≤ (planarBound b L c₀ k J T D : ℝ) := by
        simp only [planarBound, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_pow]
        nlinarith [show 0 ≤ (T : ℝ) * ((1 + 2 * D) * allSlotsBound b L k J) by positivity]
  · let n : ℕ := ⌊t - 1⌋₊
    have hl : (n : ℝ) + 1 ≤ t := by
      have := Nat.floor_le (show 0 ≤ t - 1 by linarith)
      dsimp [n]; linarith
    have hu : t ≤ (n : ℝ) + 2 := by
      have := Nat.lt_floor_add_one (t - 1)
      dsimp [n]; linarith
    calc
      _ ≤ (1 + t) ^ J * ((T : ℝ) * (1 + 2 * D) * slotSize b L k n) :=
        mul_le_mul_of_nonneg_left
          (field_slot_derivative_bound hb L c₀ r k n F H hF hH hT hD hl hu y) hweight
      _ = (T : ℝ) * (1 + 2 * D) * ((1 + t) ^ J * slotSize b L k n) := by ring
      _ ≤ (T : ℝ) * (1 + 2 * D) * allSlotsBound b L k J :=
        mul_le_mul_of_nonneg_left (weighted_slotSize_bound_all hb L k J n ht hu) (by positivity)
      _ ≤ (planarBound b L c₀ k J T D : ℝ) := hbudget

theorem field_rapid {b : ℕ} (hb : 2 ≤ b) (L c₀ r k J : ℕ) (F H : ℕ → ℤ → ℝ)
    (hF : ∀ m j, |F m j| ≤ (capacity b L (m + 1) : ℝ))
    (hH : ∀ m j, |H m j| ≤ 1) :
    ∃ C : ℕ, ∀ t : ℝ, 0 ≤ t → ∀ y : ℝ,
      ‖mixedPartial r k (schedule (coefficients b L c₀ F H)) t y‖ ≤ (C : ℝ) / (1 + t) ^ J := by
  obtain ⟨T, D, hT, hD⟩ := profile_derivative_bounds r k
  refine ⟨planarBound b L c₀ k J T D, fun t ht y => ?_⟩
  apply (le_div_iff₀ (by positivity : 0 < (1 + t) ^ J)).mpr
  simpa only [mul_comm] using field_weighted_derivative_bound hb L c₀ r k J T D F H hF hH hT hD ht y

end Planar

end
end PeriodicLattice

end OAI
