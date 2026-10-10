import Mathlib

namespace OAI

/-!
# Critical SK equilibrium starts, covariance, and mixing lower bounds

The zero-field model has independent Gaussian edge couplings of variance `1 / n`.
Continuous heat bath updates each site at rate one; a discrete attempt chooses a
site uniformly. Distances and mixing times use total variation threshold `1 / 4`.
-/

noncomputable section

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter

namespace CriticalSK

abbrev Spin (n : ℕ) := Fin n → Bool

abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

abbrev Disorder (n : ℕ) := Edge n → ℝ

def spinValue (b : Bool) : ℝ := if b then 1 else -1

def hamiltonian {n : ℕ} (W : Disorder n) (x : Spin n) : ℝ :=
  ∑ e : Edge n, W e * spinValue (x e.val.1) * spinValue (x e.val.2)

def partition {n : ℕ} (W : Disorder n) : ℝ :=
  ∑ x : Spin n, Real.exp (hamiltonian W x)

def gibbs {n : ℕ} (W : Disorder n) (x : Spin n) : ℝ :=
  Real.exp (hamiltonian W x) / partition W

def disorderLaw (n : ℕ) : Measure (Disorder n) :=
  Measure.pi fun _ : Edge n => gaussianReal 0 (n : ℝ≥0)⁻¹

def sameExcept {n : ℕ} (i : Fin n) (x y : Spin n) : Prop :=
  ∀ j, j ≠ i → y j = x j

instance {n : ℕ} (i : Fin n) (x y : Spin n) : Decidable (sameExcept i x y) :=
  Classical.propDecidable _

def siteKernel {n : ℕ} (W : Disorder n) (i : Fin n) : Matrix (Spin n) (Spin n) ℝ :=
  fun x y => if sameExcept i x y then
    gibbs W y / (∑ z : Spin n, if sameExcept i x z then gibbs W z else 0)
  else 0

def discreteKernel {n : ℕ} (W : Disorder n) : Matrix (Spin n) (Spin n) ℝ :=
  (n : ℝ)⁻¹ • ∑ i : Fin n, siteKernel W i

def generator {n : ℕ} (W : Disorder n) : Matrix (Spin n) (Spin n) ℝ :=
  ∑ i : Fin n, (siteKernel W i - 1)

def continuousKernel {n : ℕ} (W : Disorder n) (t : ℝ) :
    Matrix (Spin n) (Spin n) ℝ :=
  NormedSpace.exp (t • generator W)

def totalVariation {n : ℕ} (W : Disorder n) (p : Spin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ y : Spin n, |p y - gibbs W y|

def continuousDistance {n : ℕ} (W : Disorder n) (t : ℝ) (x : Spin n) : ℝ :=
  totalVariation W (continuousKernel W t x)

def discreteDistance {n : ℕ} (W : Disorder n) (k : ℕ) (x : Spin n) : ℝ :=
  totalVariation W ((discreteKernel W ^ k) x)

def continuousMixingTime {n : ℕ} (W : Disorder n) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ ∀ x, continuousDistance W t x ≤ 1 / 4}

def discreteMixingTime {n : ℕ} (W : Disorder n) : ℕ :=
  sInf {k : ℕ | ∀ x, discreteDistance W k x ≤ 1 / 4}

def mean {n : ℕ} (W : Disorder n) (f : Spin n → ℝ) : ℝ :=
  ∑ x : Spin n, gibbs W x * f x

def variance {n : ℕ} (W : Disorder n) (f : Spin n → ℝ) : ℝ :=
  mean W (fun x => (f x - mean W f) ^ 2)

def dirichlet {n : ℕ} (W : Disorder n) (f : Spin n → ℝ) : ℝ :=
  ∑ i : Fin n, mean W (fun x => (f x - ∑ y : Spin n, siteKernel W i x y * f y) ^ 2)

def linearObservable {n : ℕ} (a : Fin n → ℝ) (x : Spin n) : ℝ :=
  ∑ i : Fin n, a i * spinValue (x i)

def covariance {n : ℕ} (W : Disorder n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => mean W (fun x =>
    (spinValue (x i) - mean W (fun y => spinValue (y i))) *
    (spinValue (x j) - mean W (fun y => spinValue (y j))))

def covarianceNorm {n : ℕ} (W : Disorder n) : ℝ :=
  ‖(covariance W).toEuclideanLin.toContinuousLinearMap‖

/-- The supremum of variance divided by the rate-one Dirichlet form over nonzero
linear spin observables. -/
def linearRayleigh {n : ℕ} (W : Disorder n) : ℝ :=
  sSup {r : ℝ | ∃ a : Fin n → ℝ, a ≠ 0 ∧
    r = variance W (linearObservable a) / dirichlet W (linearObservable a)}

/-- Gibbs mass of realized initial states still farther than `1 / 4` from equilibrium. -/
def continuousGoodMass {n : ℕ} (W : Disorder n) (t : ℝ) : ℝ :=
  ∑ x : Spin n, if 1 / 4 < continuousDistance W t x then gibbs W x else 0

/-- Gibbs mass of realized initial states still farther than `1 / 4` after `k` attempts. -/
def discreteGoodMass {n : ℕ} (W : Disorder n) (k : ℕ) : ℝ :=
  ∑ x : Spin n, if 1 / 4 < discreteDistance W k x then gibbs W x else 0

/-- For deterministic nonnegative times `o(n^(2/3))` and attempt counts `o(n^(5/3))`,
the Gibbs mass of obstructed initial states tends to one in disorder probability. -/
theorem realized_equilibrium_initial_states :
    (∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) →
      Tendsto (fun n => t n / (n : ℝ) ^ ((2 : ℝ) / 3)) atTop (𝓝 0) →
      ∀ δ : ℝ, 0 < δ →
        Tendsto (fun n => (disorderLaw n {W |
          δ ≤ |continuousGoodMass W (t n) - 1|}).toReal) atTop (𝓝 0)) ∧
    (∀ k : ℕ → ℕ,
      Tendsto (fun n => (k n : ℝ) / (n : ℝ) ^ ((5 : ℝ) / 3)) atTop (𝓝 0) →
      ∀ δ : ℝ, 0 < δ →
        Tendsto (fun n => (disorderLaw n {W |
          δ ≤ |discreteGoodMass W (k n) - 1|}).toReal) atTop (𝓝 0)) := by
  sorry

/-- Both the covariance operator norm and the linear inverse-Rayleigh supremum lie
between `n^(2/3) / M n` and `M n * n^(2/3)` with probability tending to one. -/
theorem covariance_and_linear_tests (M : ℕ → ℝ)
    (hMpos : ∀ n, 0 < M n) (hM : Tendsto M atTop atTop) :
    Tendsto (fun n : ℕ => (disorderLaw n {W |
      (n : ℝ) ^ ((2 : ℝ) / 3) / M n ≤ covarianceNorm W ∧
      covarianceNorm W ≤ M n * (n : ℝ) ^ ((2 : ℝ) / 3) ∧
      (n : ℝ) ^ ((2 : ℝ) / 3) / M n ≤ linearRayleigh W ∧
      linearRayleigh W ≤ M n * (n : ℝ) ^ ((2 : ℝ) / 3)}).toReal) atTop (𝓝 1) := by
  sorry

/-- Worst-start mixing takes at least `n^(2/3-ε)` continuous time and
`n^(5/3-ε)` discrete attempts with probability tending to one. -/
theorem critical_mixing_lower_bounds (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (disorderLaw n).real {W |
      (n : ℝ) ^ (2 / 3 - ε) ≤ continuousMixingTime W}) atTop (𝓝 1) ∧
    Tendsto (fun n => (disorderLaw n).real {W |
      (n : ℝ) ^ (5 / 3 - ε) ≤ (discreteMixingTime W : ℝ)}) atTop (𝓝 1) := by
  sorry

end CriticalSK

end

end OAI
