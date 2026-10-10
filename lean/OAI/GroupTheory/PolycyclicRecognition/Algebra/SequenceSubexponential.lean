import OAI.GroupTheory.PolycyclicRecognition.Algebra.SubexponentialBounds
import Mathlib.Data.Nat.Find

namespace OAI

/-! # Subexponential estimates along the actual sequence of profile scales -/

noncomputable section

namespace PolycyclicRecognition

open Filter
open scoped Topology

def HasSubexponentialLowerBoundSeq (scale f : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, Real.exp (-ε * scale n) ≤ f n

def HasSubexponentialUpperBoundSeq (scale f : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, f n ≤ Real.exp (ε * scale n)

theorem HasSubexponentialLowerBound.along_sequence {f : ℝ → ℝ}
    (hf : HasSubexponentialLowerBound f) {scale : ℕ → ℝ}
    (hs : Tendsto scale atTop atTop) : HasSubexponentialLowerBoundSeq scale (f ∘ scale) :=
  fun ε hε => hs.eventually (hf ε hε)

theorem HasSubexponentialUpperBound.along_sequence {f : ℝ → ℝ}
    (hf : HasSubexponentialUpperBound f) {scale : ℕ → ℝ}
    (hs : Tendsto scale atTop atTop) : HasSubexponentialUpperBoundSeq scale (f ∘ scale) :=
  fun ε hε => hs.eventually (hf ε hε)

theorem HasSubexponentialLowerBoundSeq.eventually_pos {scale f : ℕ → ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) : ∀ᶠ n in atTop, 0 < f n :=
  (hf 1 zero_lt_one).mono (fun _ h => (Real.exp_pos _).trans_le h)

theorem HasSubexponentialLowerBoundSeq.mono {scale f g : ℕ → ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hfg : f ≤ᶠ[atTop] g) :
    HasSubexponentialLowerBoundSeq scale g := by
  intro ε hε
  filter_upwards [hf ε hε, hfg] with n hn hfg
  exact hn.trans hfg

theorem HasSubexponentialLowerBoundSeq.mul {scale f g : ℕ → ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hg : HasSubexponentialLowerBoundSeq scale g) :
    HasSubexponentialLowerBoundSeq scale (fun n => f n * g n) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (half_pos hε), hg (ε / 2) (half_pos hε)] with n hn hm
  calc
    Real.exp (-ε * scale n) = Real.exp (-(ε / 2) * scale n) *
        Real.exp (-(ε / 2) * scale n) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ f n * g n := mul_le_mul hn hm (Real.exp_pos _).le ((Real.exp_pos _).trans_le hn).le

theorem HasSubexponentialLowerBoundSeq.div {scale f g : ℕ → ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hg : HasSubexponentialUpperBoundSeq scale g)
    (hg0 : ∀ᶠ n in atTop, 0 < g n) :
    HasSubexponentialLowerBoundSeq scale (fun n => f n / g n) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (half_pos hε), hg (ε / 2) (half_pos hε), hg0] with n hn hm h0
  calc
    Real.exp (-ε * scale n) = Real.exp (-(ε / 2) * scale n) /
        Real.exp (ε / 2 * scale n) := by rw [← Real.exp_sub]; congr 1; ring
    _ ≤ f n / g n := div_le_div₀ ((Real.exp_pos _).trans_le hn).le hn h0 hm

theorem exists_slow_sequence_selection (P : ℕ → ℕ → Prop)
    (hP : ∀ j, ∀ᶠ n in atTop, P j n) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧ ∀ᶠ n in atTop, P (k n) n := by
  classical
  choose N hN using fun j => eventually_atTop.mp (hP j)
  let k : ℕ → ℕ := fun n => Nat.findGreatest (fun j => N j ≤ n) n
  have hk : Tendsto k atTop atTop := by
    apply tendsto_atTop.mpr
    intro j
    filter_upwards [eventually_ge_atTop (N j), eventually_ge_atTop j] with n hn hj
    exact Nat.le_findGreatest hj hn
  refine ⟨k, hk, ?_⟩
  filter_upwards [eventually_ge_atTop (N 0)] with n hn
  exact hN (k n) n (Nat.findGreatest_spec (P := fun j => N j ≤ n)
    (n := n) (m := 0) (Nat.zero_le _) hn)

theorem exists_slow_sequence_subexponential_mass
    (scale : ℕ → ℝ) (hs : Tendsto scale atTop atTop) (mass : ℕ → ℕ → ℝ)
    (hmass : ∀ j, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c ≤ mass j n) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧
      HasSubexponentialLowerBoundSeq scale (fun n => mass (k n) n) := by
  have hgood (j : ℕ) : ∀ᶠ n in atTop,
      Real.exp (-(1 / ((j : ℝ) + 1)) * scale n) ≤ mass j n := by
    obtain ⟨c, hc, he⟩ := hmass j
    filter_upwards [((subexponential_lower_const hc).along_sequence hs)
      (1 / ((j : ℝ) + 1)) (by positivity), he] with n hn hm
    exact hn.trans hm
  obtain ⟨k, hk, he⟩ := exists_slow_sequence_selection _ hgood
  refine ⟨k, hk, ?_⟩
  intro ε hε
  have ht : Tendsto (fun n => 1 / ((k n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hk
  filter_upwards [he, ht.eventually (eventually_lt_nhds hε),
    hs.eventually (eventually_ge_atTop (0 : ℝ))] with n hn hsmall hpos
  apply le_trans _ hn
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hsmall.le) hpos)

theorem exponent_le_of_sequence_subexponential_bounds
    {scale f g : ℕ → ℝ} (hs : Tendsto scale atTop atTop) {p q : ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hg : HasSubexponentialUpperBoundSeq scale g)
    (hbound : ∀ᶠ n in atTop, f n * Real.exp (scale n * p) ≤ g n * Real.exp (scale n * q)) :
    p ≤ q := by
  by_contra h
  have hpq : q < p := lt_of_not_ge h
  let ε := (p - q) / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨n, hn, hm, hb, hnpos⟩ := ((hf ε hε).and ((hg ε hε).and
    (hbound.and (hs.eventually (eventually_gt_atTop (0 : ℝ)))))).exists
  have he : Real.exp ((p - ε) * scale n) ≤ Real.exp ((q + ε) * scale n) := calc
    _ = Real.exp (-ε * scale n) * Real.exp (scale n * p) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ f n * Real.exp (scale n * p) := mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
    _ ≤ g n * Real.exp (scale n * q) := hb
    _ ≤ Real.exp (ε * scale n) * Real.exp (scale n * q) :=
      mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hh := Real.exp_le_exp.mp he
  have hgap : 0 < p - q - 2 * ε := by dsimp [ε]; linarith
  have hprod := mul_pos hgap hnpos
  nlinarith

end PolycyclicRecognition

end

end OAI
