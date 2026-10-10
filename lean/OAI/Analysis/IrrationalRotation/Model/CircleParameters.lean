import OAI.Analysis.IrrationalRotation.Model.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Data.Int.Interval

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Invariant233

structure CircleParameterData where
  m : ℕ → ℕ
  K : ℕ → ℕ
  G : ℕ → ℕ
  q : ℕ → ℕ
  L : ℕ → ℝ
  C : ℕ → ℝ
  ε : ℕ → ℝ
  height : ℕ → ℕ
  partition : ℕ → ℕ → C(Circle, ℝ)
  samples : ℕ → ℕ → Finset ℕ

namespace CircleParameterData

def rep (x : Circle) : ℝ := (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)

def delta (z : ℝ) : ℝ := min (Int.fract z) (1 - Int.fract z)

def kernelWidth (m : ℕ) : ℝ := (m : ℝ) ^ (-(3 / 5 : ℝ))

def kernel (m : ℕ) (z v : ℝ) : ℝ :=
  if (1 / (m : ℝ) ^ 2 ≤ delta z) ∧ 0 < v ∧ v < kernelWidth m * delta z
  then 1 / (kernelWidth m * delta z) else 0

def orientedKernel (endpoint : Bool) (m : ℕ) (z v : ℝ) : ℝ :=
  if endpoint then kernel m (z - v) v else kernel m z v

def blockEnd (p : CircleParameterData) (j : ℕ) : ℕ :=
  ∑ s ∈ Finset.Icc 1 j, p.m s

def blockIndex (p : CircleParameterData) (i : ℕ) : ℕ := by
  classical
  exact if h : ∃ j, i ≤ p.blockEnd j then Nat.find h else 0

def flattenedFrequency (p : CircleParameterData) (n : ℕ) : ℤ := p.q (n + 1)

def flattenedCost (p : CircleParameterData) (n : ℕ) : ℝ :=
  p.C (p.blockIndex (n + 1))

def block (p : CircleParameterData) (j : ℕ) : Finset ℕ :=
  Finset.Icc (p.blockEnd (j - 1) + 1) (p.blockEnd j)

def N (p : CircleParameterData) (j : ℕ) : ℝ := (p.m j : ℝ) * p.K j

def a (p : CircleParameterData) (j : ℕ) : ℝ := (p.G j : ℝ) / p.m j

def b (p : CircleParameterData) (j : ℕ) : ℝ := (p.m j : ℝ) ^ (-(19 / 20 : ℝ))

def Q (p : CircleParameterData) (j : ℕ) : ℝ :=
  (p.m j : ℝ) ^ ((7 / 10 : ℝ) * p.m j)

def kappa (j : ℕ) : ℝ := 1 / (100 * (j : ℝ))

def alpha (p : CircleParameterData) (θ : ℝ) (i : ℕ) : ℝ :=
  Int.fract ((p.q i : ℝ) * θ)

def coordinate (p : CircleParameterData) (i : ℕ) (x : Circle) : ℝ :=
  rep (p.q i • x)

def ell (p : CircleParameterData) (j : ℕ) : ℝ :=
  1 / (((j + 1 : ℕ) : ℝ) ^ 2 * (1 + (p.blockEnd (j - 1) : ℝ)) *
    (p.q (p.blockEnd (j - 1)) : ℝ))

def shift (p : CircleParameterData) (j r : ℕ) : ℝ :=
  (r : ℝ) / p.q (p.blockEnd (j - 1))

def coefficientBound (p : CircleParameterData) (j : ℕ) : ℝ :=
  Real.exp (((p.K j : ℝ) + 1) *
    ∑ s ∈ Finset.Icc 1 (j - 1), p.C s * p.m s)

def convolutionCoefficient (K : ℕ) (A B : ℤ → ℂ) (n : ℤ) : ℂ :=
  ∑ t ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), A t * B (n - t)

def samplingAverage (p : CircleParameterData) (θ : ℝ) (j r : ℕ)
    (endpoint : Bool) (x : Circle) : ℝ :=
  (1 / ((p.samples j r).card : ℝ)) *
    ∑ n ∈ p.samples j r, ∏ i ∈ p.block j,
      orientedKernel endpoint (p.m j) (p.coordinate i x)
        (Int.fract ((n : ℝ) * p.alpha θ i))

end CircleParameterData

open CircleParameterData

structure CircleParameterLaws (θ : ℝ) (p : CircleParameterData) : Prop where
  m_pos : ∀ j, 1 ≤ j → 0 < p.m j
  K_pos : ∀ j, 1 ≤ j → 0 < p.K j
  G_pos : ∀ j, 1 ≤ j → 0 < p.G j
  q_pos : ∀ i, 0 < p.q i
  L_pos : ∀ j, 1 ≤ j → 0 < p.L j
  C_pos : ∀ j, 1 ≤ j → 0 < p.C j
  epsilon_pos : ∀ j, 1 ≤ j → 0 < p.ε j
  partition_nonneg : ∀ j, 1 ≤ j → ∀ n, n ≤ p.height j →
    ∀ x, 0 ≤ p.partition j n x
  partition_sum : ∀ j, 1 ≤ j → ∀ x,
    (∑ n ∈ Finset.range (p.height j + 1), p.partition j n x) = 1
  partition_support : ∀ j, 1 ≤ j → ∀ n, n ≤ p.height j →
    ∀ x ∈ tsupport (p.partition j n),
      dist (x + (((n : ℝ) * θ : ℝ) : Circle)) 0 < 1 / (10 * (j : ℝ))
  frequency_zero : p.q 0 = 1
  frequency_increasing : StrictMono p.q
  frequency_divisible : ∀ i, p.q i ∣ p.q (i + 1)
  phase_bounds : ∀ j, 1 ≤ j → ∀ i ∈ p.block j,
    1 / p.N j < p.alpha θ i ∧ p.alpha θ i < 2 / p.N j
  frequency_ratios : ∀ j, 1 ≤ j → ∀ i ∈ p.block j,
    p.N j ≤ (p.q (i + 1) : ℝ) / p.q i
  spread_high : ∀ j, 1 ≤ j → ∀ k : ℤ,
    p.N j / 4 ≤ |(k : ℝ)| →
    |(k : ℝ)| ≤ (p.m j : ℝ) ^ ((4 / 5 : ℝ) * p.m j) →
    (p.m j : ℝ) / 20 ≤
      ((p.block j).filter (fun i =>
        1 - Int.fract ((k : ℝ) * p.alpha θ i) ∈ Set.Icc (p.b j) (1 - p.b j))).card
  spread_low : ∀ j, 1 ≤ j → ∀ k : ℤ,
    (p.G j : ℝ) * p.K j ≤ |(k : ℝ)| → |(k : ℝ)| ≤ p.N j / 4 →
    ∀ i ∈ p.block j,
      1 - Int.fract ((k : ℝ) * p.alpha θ i) ∈ Set.Icc (p.a j) (1 - p.a j)
  initial_K : p.K 1 = 100
  initial_G : p.G 1 = 1
  L_ge_one : ∀ j, 1 ≤ j → 1 ≤ p.L j
  L_monotone : ∀ j k, 1 ≤ j → j ≤ k → p.L j ≤ p.L k
  C_eq : ∀ j, 1 ≤ j → p.C j = max (p.L j) ((p.K j : ℝ) ^ 2)
  m_ge_K : ∀ j, 1 ≤ j → p.K j ≤ p.m j
  m_ge_pow : ∀ j, 1 ≤ j → 2 ^ j ≤ p.m j
  m_ge_G : ∀ j, 1 ≤ j → 4 * p.G j ≤ p.m j
  m_ge_200 : ∀ j, 1 ≤ j → 200 ≤ p.m j
  next_K : ∀ j, 1 ≤ j →
    p.K (j + 1) = ⌈(p.m j : ℝ) ^ ((3 / 4 : ℝ) * p.m j)⌉₊
  K_double : ∀ j, 1 ≤ j → 2 * p.K j < p.K (j + 1)
  next_G_gap : ∀ j, 1 ≤ j →
    (p.G (j + 1) : ℝ) * p.K (j + 1) <
      (p.m j : ℝ) ^ ((4 / 5 : ℝ) * p.m j)
  attenuation_m : ∀ j, 1 ≤ j →
    p.L j ≤ kappa j * (p.m j : ℝ) ^ (1 / 40 : ℝ)
  attenuation_G : ∀ j, 1 ≤ j →
    p.L j ≤ kappa (j + 1) * Real.sqrt (p.G (j + 1) : ℝ)
  continuity_height : ∀ j, 1 ≤ j →
    (p.height (j + 1) : ℝ) / p.K (j + 1) ≤ (1 / 2 : ℝ) ^ j
  polynomial_lower : ∀ j, 1 ≤ j → ∀ A B : ℤ → ℂ,
    Function.support A ⊆ Set.Icc (-(p.K j : ℤ)) (p.K j : ℤ) →
    Function.support B ⊆ Set.Icc (-(p.K j : ℤ)) (p.K j : ℤ) →
    (∀ n, ‖A n‖ ≤ p.coefficientBound j) →
    (∀ n, ‖B n‖ ≤ p.coefficientBound j) →
    1 / (j : ℝ) ≤ ‖A 0‖ → 1 / (j : ℝ) ≤ ‖B 0‖ →
    ∃ n ∈ Finset.Icc 0 (2 * p.K j),
      p.ε j ≤ ‖convolutionCoefficient (p.K j) A B (-(n : ℤ))‖
  polynomial_attenuation : ∀ j, 1 ≤ j →
    ((2 * p.K j + 1 : ℕ) : ℝ) * 3 * Real.exp (-p.L j / 10000) ≤ p.ε j / j
  samples_nonempty : ∀ j, 1 ≤ j → ∀ r,
    r < p.q (p.blockEnd (j - 1)) → (p.samples j r).Nonempty
  samples_positive : ∀ j, 1 ≤ j → ∀ r,
    r < p.q (p.blockEnd (j - 1)) → ∀ n ∈ p.samples j r, 0 < n
  samples_range : ∀ j, 1 ≤ j → ∀ r,
    r < p.q (p.blockEnd (j - 1)) → ∀ n ∈ p.samples j r,
      p.Q j / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ p.Q j
  samples_phase : ∀ j, 1 ≤ j → ∀ r,
    r < p.q (p.blockEnd (j - 1)) → ∀ n ∈ p.samples j r,
      Int.fract ((n : ℝ) * θ - p.shift j r) ∈ Set.Ioo 0 (p.ell j)
  sampling_L2 : ∀ j, 1 ≤ j → ∀ r,
    r < p.q (p.blockEnd (j - 1)) → ∀ endpoint : Bool,
      eLpNorm (fun x => p.samplingAverage θ j r endpoint x - 1) 2 circleMeasure <
        ENNReal.ofReal (1 / (j : ℝ))

end Invariant233

end

end OAI
