import OAI.Analysis.IrrationalRotation.Model.ProductScales
import OAI.Analysis.IrrationalRotation.Sampling.SamplingHorizon
import OAI.Analysis.IrrationalRotation.Analysis.LaurentNoncancellation

namespace OAI

noncomputable section
open scoped BigOperators
namespace Invariant233.ProductScaleConstruction

open SamplingHorizon FiniteWindow

private structure State where
  K : ℕ
  G : ℕ
  count : ℕ
  cost : ℝ
  previousL : ℝ

private structure Step (n : ℕ) (s : State) where
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

private theorem step_exists (n : ℕ) (s : State) : Nonempty (Step n s) := by
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
  obtain ⟨m, hmK, hmpow, hmG, hmlarge, hcount, hmL, hgap, _hheight, hdouble⟩ :=
    exists_stage_size (n + 1) (by omega) s.K s.G G L 0 s.count
  exact ⟨{
    m := m, Gnext := G, L := L, ε := ε
    epsilon_pos := hε, L_one := hL1, L_previous := hLprev
    gain_one := hG, gain := hgain
    m_K := by exact_mod_cast hmK
    m_pow := by exact_mod_cast hmpow
    m_G := by exact_mod_cast hmG
    m_large := hmlarge
    count_bound := hcount
    attenuation_m := hmL
    gap := hgap
    double := by exact_mod_cast hdouble
    attenuation := hL
    polynomial := hpoly }⟩

private def chooseStep (n : ℕ) (s : State) : Step n s :=
  Classical.choice (step_exists n s)

private def nextState (n : ℕ) (s : State) : State :=
  let t := chooseStep n s
  { K := ⌈(t.m : ℝ) ^ ((3 / 4 : ℝ) * t.m)⌉₊
    G := t.Gnext
    count := s.count + t.m
    cost := s.cost + max t.L ((s.K : ℝ) ^ 2) * t.m
    previousL := t.L }

private def states : ℕ → State :=
  Nat.rec ⟨100, 1, 0, 0, 0⟩ nextState

private def choices (n : ℕ) : Step n (states n) := chooseStep n (states n)

def constructed : ProductScaleData where
  m n := (choices n).m
  K n := (states n).K
  G n := (states n).G
  L n := (choices n).L
  C n := max (choices n).L (((states n).K : ℝ) ^ 2)
  ε n := (choices n).ε

private theorem states_succ (n : ℕ) : states (n + 1) = nextState n (states n) := rfl

private theorem count_eq (n : ℕ) : (states n).count = constructed.prefixCount n := by
  induction n with
  | zero => simp [states, ProductScaleData.prefixCount]
  | succ n ih =>
    change (states n).count + (choices n).m = constructed.prefixCount (n + 1)
    rw [ih]
    simp [ProductScaleData.prefixCount, Finset.sum_range_succ, constructed]

private theorem cost_eq (n : ℕ) : (states n).cost = constructed.prefixCost n := by
  induction n with
  | zero => simp [states, ProductScaleData.prefixCost]
  | succ n ih =>
    change (states n).cost + max (choices n).L (((states n).K : ℝ) ^ 2) *
      (choices n).m = constructed.prefixCost (n + 1)
    rw [ih]
    simp [ProductScaleData.prefixCost, Finset.sum_range_succ, constructed]

theorem constructed_laws : ProductScaleLaws constructed := by
  refine {
    initial_K := rfl
    initial_G := rfl
    K_pos := ?_
    G_pos := ?_
    epsilon_pos := fun n => (choices n).epsilon_pos
    L_ge_one := fun n => (choices n).L_one
    L_monotone := ?_
    C_eq := fun _ => rfl
    polynomial_lower := ?_
    polynomial_attenuation := fun n => (choices n).attenuation
    gain_attenuation := fun n => (choices n).gain
    m_ge_K := fun n => (choices n).m_K
    m_ge_pow := fun n => (choices n).m_pow
    m_ge_G := fun n => (choices n).m_G
    m_ge_100 := fun n => le_trans (by decide) (choices n).m_large
    prefix_count_le := ?_
    m_attenuation := fun n => (choices n).attenuation_m
    next_K := fun _ => rfl
    next_gap := fun n => (choices n).gap
    K_double := fun n => (choices n).double }
  · intro n
    induction n with
    | zero => norm_num [constructed, states]
    | succ n ih =>
      have h := (choices n).double
      change 0 < ⌈((choices n).m : ℝ) ^ ((3 / 4 : ℝ) * (choices n).m)⌉₊
      omega
  · intro n
    cases n with
    | zero => norm_num [constructed, states]
    | succ n => exact Nat.zero_lt_of_lt (choices n).gain_one
  · apply monotone_nat_of_le_succ
    intro n
    exact (choices (n + 1)).L_previous
  · intro n
    unfold ProductScaleData.coefficientBound
    rw [← cost_eq n]
    exact (choices n).polynomial
  · intro n
    rw [← count_eq n]
    exact (choices n).count_bound

theorem exists_product_scales : ∃ p : ProductScaleData, ProductScaleLaws p :=
  ⟨constructed, constructed_laws⟩

end Invariant233.ProductScaleConstruction

end

end OAI
