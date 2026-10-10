import Mathlib

namespace OAI

section

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

namespace SK
abbrev Config (n : ℕ) := Fin n → Bool
abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev Disorder (n : ℕ) := Edge n → ℝ

def spin (b : Bool) : ℝ := if b then 1 else -1

def hamiltonian {n : ℕ} (J : Disorder n) (x : Config n) : ℝ :=
  (∑ e : Edge n, J e * spin (x e.val.1) * spin (x e.val.2)) / Real.sqrt n

def partition {n : ℕ} (β : ℝ) (J : Disorder n) : ℝ :=
  ∑ x : Config n, Real.exp (β * hamiltonian J x)

def gibbs {n : ℕ} (β : ℝ) (J : Disorder n) (x : Config n) : ℝ :=
  Real.exp (β * hamiltonian J x) / partition β J

def coupling {n : ℕ} (J : Disorder n) (i j : Fin n) : ℝ :=
  if h : i < j then J ⟨(i, j), h⟩ else
    if h : j < i then J ⟨(j, i), h⟩ else 0

def localField {n : ℕ} (J : Disorder n) (x : Config n) (i : Fin n) : ℝ :=
  (∑ j : Fin n, coupling J i j * spin (x j)) / Real.sqrt n

def heatBath {n : ℕ} (β : ℝ) (J : Disorder n) (x y : Config n) : ℝ :=
  (∑ i : Fin n, if Function.update x i (y i) = y then
    Real.exp (β * spin (y i) * localField J x i) /
      (2 * Real.cosh (β * localField J x i)) else 0) / n

def discreteKernel {n : ℕ} (β : ℝ) (J : Disorder n) : ℕ → Config n → Config n → ℝ
  | 0, x, y => if x = y then 1 else 0
  | k + 1, x, y => ∑ z : Config n, heatBath β J x z * discreteKernel β J k z y

def continuousKernel {n : ℕ} (β : ℝ) (J : Disorder n) (t : ℝ)
    (x y : Config n) : ℝ :=
  ∑' k : ℕ, (Real.exp (-(n : ℝ) * t) * ((n : ℝ) * t) ^ k /
    (Nat.factorial k : ℝ)) * discreteKernel β J k x y

def discreteDistance {n : ℕ} (β : ℝ) (J : Disorder n)
    (x : Config n) (k : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∑ y : Config n, |discreteKernel β J k x y - gibbs β J y|

def continuousDistance {n : ℕ} (β : ℝ) (J : Disorder n)
    (x : Config n) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ y : Config n, |continuousKernel β J t x y - gibbs β J y|

def disorderLaw (n : ℕ) : Measure (Disorder n) :=
  Measure.pi (fun _ : Edge n => gaussianReal 0 1)

def kappa : ℝ := 1 / 10000

def timeScale (n : ℕ) : ℝ := Real.exp ((n : ℝ) ^ kappa)

def continuousBadMass (β : ℝ) (n : ℕ) : ℝ :=
  ∫ J : Disorder n, (∑ x : Config n, if 1 / 4 < continuousDistance β J x (timeScale n)
    then gibbs β J x else 0) ∂disorderLaw n

def discreteBadMass (β : ℝ) (n : ℕ) : ℝ :=
  ∫ J : Disorder n, (∑ x : Config n, if 1 / 4 < discreteDistance β J x ⌊timeScale n⌋₊
    then gibbs β J x else 0) ∂disorderLaw n

end SK
end
end
end

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

namespace SK

theorem main (β : ℝ) (hβ : 1 < β) :
    Tendsto (continuousBadMass β) atTop (𝓝 1) ∧
    Tendsto (discreteBadMass β) atTop (𝓝 1) := by
  sorry

end SK
end

end OAI
