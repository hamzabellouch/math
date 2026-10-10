import OAI.Analysis.IrrationalRotation.Model.ProductScales
import OAI.Analysis.IrrationalRotation.Sampling.SamplingHorizon
import OAI.Analysis.IrrationalRotation.Analysis.LaurentNoncancellation
import OAI.Analysis.IrrationalRotation.Analysis.OrbitPartition
import OAI.Analysis.IrrationalRotation.Product.ProductScaleConsequences
import OAI.Analysis.IrrationalRotation.Analysis.GeometricTails

namespace OAI

noncomputable section
open scoped BigOperators
namespace Invariant233.HeightScaleConstruction

open SamplingHorizon FiniteWindow

variable (height lower : ℕ → ℕ)

private structure State where
  K : ℕ
  G : ℕ
  count : ℕ
  cost : ℝ
  previousL : ℝ

private structure Step (height lower : ℕ → ℕ) (n : ℕ) (s : State) where
  m : ℕ
  Gnext : ℕ
  L : ℝ
  ε : ℝ
  epsilon_pos : 0 < ε
  L_one : 1 ≤ L
  L_previous : s.previousL ≤ L
  gain_one : 1 ≤ Gnext
  gain : L ≤ ProductScaleData.kappa (n + 1) * Real.sqrt (Gnext : ℝ)
  m_K : s.K ≤ m
  m_pow : 2 ^ (n + 1) ≤ m
  m_G : 4 * s.G ≤ m
  m_large : 200 ≤ m
  m_lower : lower n ≤ m
  height_bound : (height (n + 1) : ℝ) /
    (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) ≤ (1 / 2 : ℝ) ^ (n + 1)
  count_bound : (s.count : ℝ) ≤ (m : ℝ) / 100
  attenuation_m : L ≤ ProductScaleData.kappa n * (m : ℝ) ^ (1 / 40 : ℝ)
  gap : (Gnext : ℝ) * (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) <
    (m : ℝ) ^ ((4 / 5 : ℝ) * m)
  double : 2 * s.K < ⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊
  attenuation : ((2 * s.K + 1 : ℕ) : ℝ) * 3 * Real.exp (-L / 10000) ≤
    ε / ((n + 1 : ℕ) : ℝ)
  polynomial : ∀ A B : ℤ → ℂ,
    (∀ i, |i| ≤ (s.K : ℤ) → ‖A i‖ ≤ Real.exp (((s.K : ℝ) + 1) * s.cost)) →
    (∀ i, |i| ≤ (s.K : ℤ) → ‖B i‖ ≤ Real.exp (((s.K : ℝ) + 1) * s.cost)) →
    1 / ((n + 1 : ℕ) : ℝ) ≤ ‖A 0‖ → 1 / ((n + 1 : ℕ) : ℝ) ≤ ‖B 0‖ →
    ∃ i : ℕ, i ≤ 2 * s.K ∧ ε ≤ ‖convolution s.K A B i‖

private theorem step_exists (n : ℕ) (s : State) : Nonempty (Step height lower n s) := by
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  obtain ⟨ε, hε, hpoly⟩ := uniform_convolution_lower_bound s.K
    (Real.exp (((s.K : ℝ) + 1) * s.cost)) (1 / ((n + 1 : ℕ) : ℝ)) (by positivity)
  obtain ⟨L, hL1, hLprev, hL⟩ := exists_attenuation
    (((2 * s.K + 1 : ℕ) : ℝ) * 3) s.previousL
      (ε / ((n + 1 : ℕ) : ℝ)) (div_pos hε hn)
  have hk : 0 < ProductScaleData.kappa (n + 1) := by
    unfold ProductScaleData.kappa
    positivity
  obtain ⟨G, hG, hgain⟩ := exists_next_gain (ProductScaleData.kappa (n + 1)) L hk
  obtain ⟨m, hmstage, hmlower⟩ := ((eventually_stage_size (n + 1) (by omega)
    s.K s.G G L (height (n + 1)) s.count).and
      (Filter.eventually_ge_atTop (lower n))).exists
  obtain ⟨hmK, hmpow, hmG, hmlarge, hcount, hmL, hgap, hheight, hdouble⟩ := hmstage
  exact ⟨{
    m := m, Gnext := G, L := L, ε := ε
    epsilon_pos := hε, L_one := hL1, L_previous := hLprev
    gain_one := hG, gain := hgain
    m_K := by exact_mod_cast hmK
    m_pow := by exact_mod_cast hmpow
    m_G := by exact_mod_cast hmG
    m_large := hmlarge
    m_lower := hmlower
    height_bound := hheight
    count_bound := hcount
    attenuation_m := hmL
    gap := hgap
    double := by exact_mod_cast hdouble
    attenuation := hL
    polynomial := hpoly }⟩

private def chooseStep (n : ℕ) (s : State) : Step height lower n s :=
  Classical.choice (step_exists height lower n s)

private def nextState (n : ℕ) (s : State) : State :=
  let t := chooseStep height lower n s
  { K := ⌈(t.m : ℝ) ^ ((3 / 4 : ℝ) * t.m)⌉₊
    G := t.Gnext
    count := s.count + t.m
    cost := s.cost + max t.L ((s.K : ℝ) ^ 2) * t.m
    previousL := t.L }

private def states : ℕ → State :=
  Nat.rec ⟨100, 1, 0, 0, 0⟩ (nextState height lower)

private def choices (n : ℕ) : Step height lower n (states height lower n) :=
  chooseStep height lower n (states height lower n)

def constructed : ProductScaleData where
  m n := (choices height lower n).m
  K n := (states height lower n).K
  G n := (states height lower n).G
  L n := (choices height lower n).L
  C n := max (choices height lower n).L (((states height lower n).K : ℝ) ^ 2)
  ε n := (choices height lower n).ε

private theorem count_eq (n : ℕ) : (states height lower n).count = (constructed height lower).prefixCount n := by
  induction n with
  | zero => simp [states, ProductScaleData.prefixCount]
  | succ n ih =>
    change (states height lower n).count + (choices height lower n).m = (constructed height lower).prefixCount (n + 1)
    rw [ih]
    simp [ProductScaleData.prefixCount, Finset.sum_range_succ, constructed]

private theorem cost_eq (n : ℕ) : (states height lower n).cost = (constructed height lower).prefixCost n := by
  induction n with
  | zero => simp [states, ProductScaleData.prefixCost]
  | succ n ih =>
    change (states height lower n).cost + max (choices height lower n).L (((states height lower n).K : ℝ) ^ 2) *
      (choices height lower n).m = (constructed height lower).prefixCost (n + 1)
    rw [ih]
    simp [ProductScaleData.prefixCost, Finset.sum_range_succ, constructed]

theorem constructed_laws : ProductScaleLaws (constructed height lower) := by
  refine {
    initial_K := rfl
    initial_G := rfl
    K_pos := ?_
    G_pos := ?_
    epsilon_pos := fun n => (choices height lower n).epsilon_pos
    L_ge_one := fun n => (choices height lower n).L_one
    L_monotone := ?_
    C_eq := fun _ => rfl
    polynomial_lower := ?_
    polynomial_attenuation := fun n => (choices height lower n).attenuation
    gain_attenuation := fun n => (choices height lower n).gain
    m_ge_K := fun n => (choices height lower n).m_K
    m_ge_pow := fun n => (choices height lower n).m_pow
    m_ge_G := fun n => (choices height lower n).m_G
    m_ge_100 := fun n => le_trans (by decide) (choices height lower n).m_large
    prefix_count_le := ?_
    m_attenuation := fun n => (choices height lower n).attenuation_m
    next_K := fun _ => rfl
    next_gap := fun n => (choices height lower n).gap
    K_double := fun n => (choices height lower n).double }
  · intro n
    induction n with
    | zero => norm_num [constructed, states]
    | succ n ih =>
      have h := (choices height lower n).double
      change 0 < ⌈((choices height lower n).m : ℝ) ^ ((3 / 4 : ℝ) * (choices height lower n).m)⌉₊
      omega
  · intro n
    cases n with
    | zero => norm_num [constructed, states]
    | succ n => exact Nat.zero_lt_of_lt (choices height lower n).gain_one
  · apply monotone_nat_of_le_succ
    intro n
    exact (choices height lower (n + 1)).L_previous
  · intro n
    unfold ProductScaleData.coefficientBound
    rw [← cost_eq height lower n]
    exact (choices height lower n).polynomial
  · intro n
    rw [← count_eq height lower n]
    exact (choices height lower n).count_bound

theorem constructed_height_bound (n : ℕ) :
    (height (n + 1) : ℝ) / (constructed height lower).K (n + 1) ≤
      (1 / 2 : ℝ) ^ (n + 1) :=
  (choices height lower n).height_bound

theorem constructed_m_ge_two_hundred (n : ℕ) :
    200 ≤ (constructed height lower).m n :=
  (choices height lower n).m_large

theorem constructed_m_ge_lower (n : ℕ) :
    lower n ≤ (constructed height lower).m n :=
  (choices height lower n).m_lower

theorem constructed_summable_height :
    Summable (fun n => (1 + (height n : ℝ)) / (constructed height lower).K n) := by
  let p := constructed height lower
  have hp : ProductScaleLaws p := constructed_laws height lower
  apply InvariantProjection.GeometricTails.summable_one_add_height_div
    hp.real_K_pos hp.real_K_double (fun n => Nat.cast_nonneg (height n))
  intro n
  exact (constructed_height_bound height lower n).trans
    (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) (Nat.le_succ n))

theorem exists_scales_with_heights :
    ∃ p : ProductScaleData, ProductScaleLaws p ∧
      (∀ n, 200 ≤ p.m n) ∧ (∀ n, lower n ≤ p.m n) ∧
      (∀ n, (height (n + 1) : ℝ) / p.K (n + 1) ≤ (1 / 2 : ℝ) ^ (n + 1)) ∧
      Summable (fun n => (1 + (height n : ℝ)) / p.K n) :=
  ⟨constructed height lower, constructed_laws height lower,
    constructed_m_ge_two_hundred height lower,
    constructed_m_ge_lower height lower,
    constructed_height_bound height lower,
    constructed_summable_height height lower⟩

theorem exists_partitions_and_scales {θ : ℝ} (hθ : Irrational θ)
    (lower : ℕ → ℕ) :
    ∃ height : ℕ → ℕ, ∃ φ : ℕ → ℕ → C(AddCircle (1 : ℝ), ℝ),
    ∃ p : ProductScaleData,
      (∀ j n x, 0 ≤ φ j n x) ∧
      (∀ j x, ∑ n ∈ Finset.range (height j + 1), φ j n x = 1) ∧
      (∀ j, 1 ≤ j → ∀ n, ∀ x ∈ tsupport (φ j n),
        dist (x + (((n : ℝ) * θ : ℝ) : AddCircle (1 : ℝ))) 0 <
          1 / (10 * (j : ℝ))) ∧
      (∀ j n, height j < n → φ j n = 0) ∧
      ProductScaleLaws p ∧ (∀ n, 200 ≤ p.m n) ∧
      (∀ n, lower n ≤ p.m n) ∧
      (∀ n, (height (n + 2) : ℝ) / p.K (n + 1) ≤ (1 / 2 : ℝ) ^ (n + 1)) ∧
      Summable (fun n => (1 + (height (n + 1) : ℝ)) / p.K n) := by
  obtain ⟨height, φ, hnonneg, hsum, hsupport, hzero⟩ :=
    exists_preparatory_partitions hθ
  obtain ⟨p, hp, hm, hlower, hheight, hsummable⟩ :=
    exists_scales_with_heights (fun n => height (n + 1)) lower
  exact ⟨height, φ, p, hnonneg, hsum, hsupport, hzero, hp, hm, hlower,
    hheight, hsummable⟩

end Invariant233.HeightScaleConstruction

end

end OAI
