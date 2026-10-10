import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

namespace OAI

/-! Approximate rational bisection for a Lipschitz residual.  A numerically
ambiguous sign terminates with a certified residual bound; otherwise the
true endpoint signs are preserved.  No monotonicity or derivative lower
bound is required. -/

namespace ContinuumCoulomb.ApproximateBisection

structure Interval where
  lo : ℚ
  hi : ℚ
  settled : Bool
  deriving DecidableEq

def midpoint (s : Interval) : ℚ := (s.lo + s.hi) / 2

def width (s : Interval) : ℝ := (s.hi : ℝ) - s.lo

def step (δ : ℚ) (evaluate : ℚ → ℚ) (s : Interval) : Interval :=
  if s.settled then s
  else if δ < evaluate (midpoint s) then ⟨midpoint s, s.hi, false⟩
  else if evaluate (midpoint s) < -δ then ⟨s.lo, midpoint s, false⟩
  else ⟨midpoint s, midpoint s, true⟩

def initial (a b : ℚ) : Interval := ⟨a, b, false⟩

def run (δ : ℚ) (evaluate : ℚ → ℚ) (a b : ℚ) (n : ℕ) : Interval :=
  (step δ evaluate)^[n] (initial a b)

@[simp] theorem midpoint_cast (s : Interval) :
    (midpoint s : ℝ) = ((s.lo : ℝ) + s.hi) / 2 := by
  simp [midpoint]

theorem midpoint_mem (s : Interval) (h : s.lo ≤ s.hi) :
    s.lo ≤ midpoint s ∧ midpoint s ≤ s.hi := by
  dsimp [midpoint]
  constructor <;> linarith

/-- The invariant concerns actual residual values, not numerical signs. -/
structure Invariant (a b : ℚ) (f : ℝ → ℝ) (δ : ℚ) (s : Interval) : Prop where
  lower : a ≤ s.lo
  upper : s.hi ≤ b
  ordered : s.lo ≤ s.hi
  certified : s.settled = true → s.lo = s.hi ∧ |f s.lo| ≤ 2 * (δ : ℝ)
  signs : s.settled = false → 0 ≤ f s.lo ∧ f s.hi ≤ 0

theorem initial_invariant {a b δ : ℚ} {f : ℝ → ℝ}
    (hab : a ≤ b) (ha : 0 ≤ f a) (hb : f b ≤ 0) :
    Invariant a b f δ (initial a b) := by
  refine ⟨le_rfl, le_rfl, hab, ?_, ?_⟩
  · simp [initial]
  · intro _
    exact ⟨ha, hb⟩

theorem step_invariant {a b δ : ℚ} {f : ℝ → ℝ} {evaluate : ℚ → ℚ}
    (_hδ : 0 ≤ δ)
    (heval : ∀ q ∈ Set.Icc a b, |(evaluate q : ℝ) - f q| ≤ (δ : ℝ))
    {s : Interval} (hs : Invariant a b f δ s) :
    Invariant a b f δ (step δ evaluate s) := by
  have hm := midpoint_mem s hs.ordered
  have he := abs_le.mp (heval (midpoint s) ⟨hs.lower.trans hm.1, hm.2.trans hs.upper⟩)
  unfold step
  split_ifs with hd hp hn
  · exact hs
  · have hp' : (δ : ℝ) < evaluate (midpoint s) := by exact_mod_cast hp
    refine ⟨hs.lower.trans hm.1, hs.upper, hm.2, ?_, ?_⟩
    · simp
    · intro _
      exact ⟨by linarith [he.2], (hs.signs (by simpa using hd)).2⟩
  · have hn' : (evaluate (midpoint s) : ℝ) < -(δ : ℝ) := by exact_mod_cast hn
    refine ⟨hs.lower, hm.2.trans hs.upper, hm.1, ?_, ?_⟩
    · simp
    · intro _
      exact ⟨(hs.signs (by simpa using hd)).1, by linarith [he.1]⟩
  · have hp' : (evaluate (midpoint s) : ℝ) ≤ δ := by exact_mod_cast le_of_not_gt hp
    have hn' : -(δ : ℝ) ≤ evaluate (midpoint s) := by exact_mod_cast le_of_not_gt hn
    refine ⟨hs.lower.trans hm.1, hm.2.trans hs.upper, le_rfl, ?_, ?_⟩
    · intro _
      refine ⟨rfl, abs_le.mpr ?_⟩
      constructor <;> linarith [he.1, he.2]
    · simp

theorem step_width {a b δ : ℚ} {f : ℝ → ℝ} {evaluate : ℚ → ℚ}
    {s : Interval} (hs : Invariant a b f δ s) :
    width (step δ evaluate s) ≤ width s / 2 := by
  have ho : (s.lo : ℝ) ≤ s.hi := by exact_mod_cast hs.ordered
  unfold step
  split_ifs with hd hp hn
  · have heq := (hs.certified hd).1
    simp only [width, heq, sub_self, zero_div, le_refl]
  · simp only [width, midpoint_cast]
    linarith
  · simp only [width, midpoint_cast]
    linarith
  · simp only [width, sub_self]
    linarith

theorem run_invariant {a b δ : ℚ} {f : ℝ → ℝ} {evaluate : ℚ → ℚ}
    (hδ : 0 ≤ δ) (hab : a ≤ b) (ha : 0 ≤ f a) (hb : f b ≤ 0)
    (heval : ∀ q ∈ Set.Icc a b, |(evaluate q : ℝ) - f q| ≤ (δ : ℝ)) (n : ℕ) :
    Invariant a b f δ (run δ evaluate a b n) := by
  induction n with
  | zero => exact initial_invariant hab ha hb
  | succ n ih =>
    change Invariant a b f δ ((step δ evaluate)^[n + 1] (initial a b))
    rw [Function.iterate_succ_apply']
    exact step_invariant hδ heval ih

theorem run_width {a b δ : ℚ} {f : ℝ → ℝ} {evaluate : ℚ → ℚ}
    (hδ : 0 ≤ δ) (hab : a ≤ b) (ha : 0 ≤ f a) (hb : f b ≤ 0)
    (heval : ∀ q ∈ Set.Icc a b, |(evaluate q : ℝ) - f q| ≤ (δ : ℝ)) (n : ℕ) :
    width (run δ evaluate a b n) ≤ ((b : ℝ) - a) / 2 ^ n := by
  induction n with
  | zero => simp [run, initial, width]
  | succ n ih =>
    have hw := step_width (evaluate := evaluate) (run_invariant hδ hab ha hb heval n)
    have hrun : run δ evaluate a b (n + 1) = step δ evaluate (run δ evaluate a b n) :=
      Function.iterate_succ_apply' _ _ _
    rw [hrun]
    calc
      width (step δ evaluate (run δ evaluate a b n)) ≤
          width (run δ evaluate a b n) / 2 := hw
      _ ≤ (((b : ℝ) - a) / 2 ^ n) / 2 := div_le_div_of_nonneg_right ih (by norm_num)
      _ = ((b : ℝ) - a) / 2 ^ (n + 1) := by rw [pow_succ, div_div]

theorem invariant_residual {a b δ : ℚ} {f : ℝ → ℝ} {L : ℝ}
    (hδ : 0 ≤ δ) (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Set.Icc (a : ℝ) b, ∀ y ∈ Set.Icc (a : ℝ) b,
      |f x - f y| ≤ L * |x - y|)
    {s : Interval} (hs : Invariant a b f δ s) :
    |f (midpoint s)| ≤ 2 * (δ : ℝ) + L * width s := by
  have hl : (a : ℝ) ≤ s.lo := by exact_mod_cast hs.lower
  have hu : (s.hi : ℝ) ≤ b := by exact_mod_cast hs.upper
  have ho : (s.lo : ℝ) ≤ s.hi := by exact_mod_cast hs.ordered
  have hm := midpoint_mem s hs.ordered
  have hmlo : (s.lo : ℝ) ≤ midpoint s := by exact_mod_cast hm.1
  have hmhi : (midpoint s : ℝ) ≤ s.hi := by exact_mod_cast hm.2
  have hw : 0 ≤ width s := sub_nonneg.mpr ho
  by_cases hd : s.settled = true
  · obtain ⟨heq, herr⟩ := hs.certified hd
    have he : midpoint s = s.lo := by simp [midpoint, heq]
    rw [he]
    exact herr.trans (le_add_of_nonneg_right (mul_nonneg hL hw))
  · have hsign := hs.signs (by simpa using hd)
    have hmemb : (midpoint s : ℝ) ∈ Set.Icc (a : ℝ) b := ⟨hl.trans hmlo, hmhi.trans hu⟩
    have hleft := hLip (midpoint s) hmemb s.lo ⟨hl, ho.trans hu⟩
    have hright := hLip (midpoint s) hmemb s.hi ⟨hl.trans ho, hu⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hmlo)] at hleft
    rw [abs_of_nonpos (sub_nonpos.mpr hmhi)] at hright
    have hlw : L * ((midpoint s : ℝ) - s.lo) ≤ L * width s :=
      mul_le_mul_of_nonneg_left (by dsimp [width]; linarith) hL
    have hrw : L * -((midpoint s : ℝ) - s.hi) ≤ L * width s :=
      mul_le_mul_of_nonneg_left (by dsimp [width]; linarith) hL
    have hδ' : 0 ≤ (δ : ℝ) := by exact_mod_cast hδ
    apply abs_le.mpr
    constructor
    · have h := (neg_le_abs (f (midpoint s) - f s.lo)).trans hleft
      linarith [hsign.1]
    · have h := (le_abs_self (f (midpoint s) - f s.hi)).trans hright
      linarith [hsign.2]

/-- After `n` steps the returned rational has residual at most numerical
ambiguity plus the Lipschitz constant times the halved interval width. -/
theorem run_residual {a b δ : ℚ} {f : ℝ → ℝ} {evaluate : ℚ → ℚ} {L : ℝ}
    (hδ : 0 ≤ δ) (hab : a ≤ b) (ha : 0 ≤ f a) (hb : f b ≤ 0) (hL : 0 ≤ L)
    (heval : ∀ q ∈ Set.Icc a b, |(evaluate q : ℝ) - f q| ≤ (δ : ℝ))
    (hLip : ∀ x ∈ Set.Icc (a : ℝ) b, ∀ y ∈ Set.Icc (a : ℝ) b,
      |f x - f y| ≤ L * |x - y|) (n : ℕ) :
    |f (midpoint (run δ evaluate a b n))| ≤
      2 * (δ : ℝ) + L * (((b : ℝ) - a) / 2 ^ n) := by
  exact (invariant_residual hδ hL hLip (run_invariant hδ hab ha hb heval n)).trans
    (add_le_add_right (mul_le_mul_of_nonneg_left (run_width hδ hab ha hb heval n) hL) _)

theorem run_mem {a b δ : ℚ} {f : ℝ → ℝ} {evaluate : ℚ → ℚ}
    (hδ : 0 ≤ δ) (hab : a ≤ b) (ha : 0 ≤ f a) (hb : f b ≤ 0)
    (heval : ∀ q ∈ Set.Icc a b, |(evaluate q : ℝ) - f q| ≤ (δ : ℝ)) (n : ℕ) :
    midpoint (run δ evaluate a b n) ∈ Set.Icc a b := by
  have hi := run_invariant hδ hab ha hb heval n
  have hm := midpoint_mem _ hi.ordered
  exact ⟨hi.lower.trans hm.1, hm.2.trans hi.upper⟩

/-- Binary magnitude bounds give a number of bisection steps linear in
the requested precision and the magnitude exponent. -/
theorem run_binary_precision {a b δ : ℚ} {f : ℝ → ℝ} {evaluate : ℚ → ℚ} {L : ℝ}
    (hδ : 0 ≤ δ) (hab : a ≤ b) (ha : 0 ≤ f a) (hb : f b ≤ 0) (hL : 0 ≤ L)
    (heval : ∀ q ∈ Set.Icc a b, |(evaluate q : ℝ) - f q| ≤ (δ : ℝ))
    (hLip : ∀ x ∈ Set.Icc (a : ℝ) b, ∀ y ∈ Set.Icc (a : ℝ) b,
      |f x - f y| ≤ L * |x - y|) (B p : ℕ)
    (hδp : (δ : ℝ) ≤ (2 ^ (p + 2))⁻¹)
    (hLB : L ≤ 2 ^ B) (hwidth : (b : ℝ) - a ≤ 2 ^ B) :
    |f (midpoint (run δ evaluate a b (2 * B + p + 1)))| ≤ (2 ^ p : ℝ)⁻¹ := by
  have hw : 0 ≤ (b : ℝ) - a := sub_nonneg.mpr (by exact_mod_cast hab)
  have hprod : L * ((b : ℝ) - a) ≤ (2 ^ B : ℝ) * 2 ^ B :=
    mul_le_mul hLB hwidth hw (by positivity)
  have hden : 0 ≤ (2 ^ (2 * B + p + 1) : ℝ)⁻¹ := by positivity
  have herror := run_residual hδ hab ha hb hL heval hLip (2 * B + p + 1)
  have hnum := mul_le_mul_of_nonneg_right hprod hden
  have hexact : 2 * (2 ^ (p + 2) : ℝ)⁻¹ +
      (2 ^ B * 2 ^ B) * (2 ^ (2 * B + p + 1) : ℝ)⁻¹ = (2 ^ p : ℝ)⁻¹ := by
    rw [show 2 * B + p + 1 = B + B + (p + 1) by omega]
    simp only [pow_add, pow_succ]
    field_simp
    ring
  calc
    |f (midpoint (run δ evaluate a b (2 * B + p + 1)))| ≤
        2 * (δ : ℝ) + (L * ((b : ℝ) - a)) * (2 ^ (2 * B + p + 1) : ℝ)⁻¹ := by
      simpa only [div_eq_mul_inv, mul_assoc] using herror
    _ ≤ 2 * (2 ^ (p + 2) : ℝ)⁻¹ +
        (2 ^ B * 2 ^ B) * (2 ^ (2 * B + p + 1) : ℝ)⁻¹ := by
      linarith
    _ = (2 ^ p : ℝ)⁻¹ := hexact

end ContinuumCoulomb.ApproximateBisection

end OAI
