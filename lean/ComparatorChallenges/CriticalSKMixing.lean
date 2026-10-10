import Mathlib

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter

noncomputable section
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

theorem critical_mixing_bounds (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (disorderLaw n {W |
      (n : ℝ) ^ ((2 : ℝ) / 3 - ε) ≤ continuousMixingTime W ∧
      continuousMixingTime W ≤ Real.exp (ε * n)}).toReal) atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ => (disorderLaw n {W |
      (n : ℝ) ^ ((5 : ℝ) / 3 - ε) ≤ (discreteMixingTime W : ℝ) ∧
      (discreteMixingTime W : ℝ) ≤ Real.exp (ε * n)}).toReal) atTop (𝓝 1) := by
  sorry

end CriticalSK
end

end OAI
