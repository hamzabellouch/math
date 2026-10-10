import Mathlib

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ProductCells

abbrev Plane := ℝ × ℝ

def closedCell (A B : ℝ) : Set Plane :=
  {p | |p.1| ≤ A ∧ |p.2| ≤ A ∧ |p.1 * p.2| ≤ B}

def openCell (A B : ℝ) : Set Plane :=
  {p | |p.1| < A ∧ |p.2| < A ∧ |p.1 * p.2| < B}

def parameterCell (tau : ℝ) : Set Plane := closedCell 1 tau

def interceptCell (tau gamma : ℝ) : Set Plane := openCell 3 ((1 + gamma) * tau)

def logarithmicCell (m : ℝ) : Set Plane := closedCell m 1

def logarithmicIntercept (m gamma : ℝ) : Set Plane := openCell (3 * m) (1 + gamma)

def dilation (m : ℝ) (p : Plane) : Plane := (m * p.1, m * p.2)

def coordinateEquiv : Plane ≃L[ℝ] (Fin 2 → ℝ) :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm

def coordinateParameterCell (tau : ℝ) : Set (Fin 2 → ℝ) :=
  coordinateEquiv '' parameterCell tau

def coordinateInterceptCell (tau gamma : ℝ) : Set (Fin 2 → ℝ) :=
  coordinateEquiv '' interceptCell tau gamma

def areaRatio (tau gamma : ℝ) : ℝ :=
  (1 + gamma) * (1 + Real.log (9 / ((1 + gamma) * tau))) /
    (1 + Real.log (1 / tau))

def CellAreaStatement : Prop :=
  ∀ A B : ℝ, 0 < A → 0 < B → B ≤ A^2 →
    IsCompact (closedCell A B) ∧ IsOpen (openCell A B) ∧
    Bornology.IsBounded (openCell A B) ∧
    volume.real (closedCell A B) = 4*B*(1+Real.log (A^2/B)) ∧
    volume.real (openCell A B) = 4*B*(1+Real.log (A^2/B)) ∧
    volume (frontier (closedCell A B)) = 0 ∧ volume (frontier (openCell A B)) = 0

def CellDilationStatement : Prop :=
  ∀ m gamma : ℝ, 1 < m →
    logarithmicCell m = dilation m '' parameterCell (1/m^2) ∧
    logarithmicIntercept m gamma = dilation m '' interceptCell (1/m^2) gamma

def CellRatioStatement : Prop :=
  (∀ tau gamma : ℝ, 0 < tau → tau < 1 → 0 ≤ gamma → (1+gamma)*tau < 1 →
    volume.real (interceptCell tau gamma) / volume.real (parameterCell tau) =
      areaRatio tau gamma) ∧
  (∀ gamma : ℝ, 0 ≤ gamma →
    Tendsto (fun tau : ℝ => areaRatio tau gamma) (𝓝[>] 0) (𝓝 (1+gamma)))

def CellParameterStatement : Prop :=
  (∀ gamma eta : ℝ, 0 ≤ gamma → gamma < eta →
    ∃ tau : ℝ, 0 < tau ∧ tau < 1 ∧ (1+gamma)*tau < 1 ∧
      areaRatio tau gamma < 1+eta) ∧
  (∀ tau eta : ℝ, 0 < tau → tau < 1 → areaRatio tau 0 < 1+eta →
    ∃ gamma : ℝ, 0 < gamma ∧ (1+gamma)*tau < 1 ∧ areaRatio tau gamma < 1+eta) ∧
  (∀ eta : ℝ, 0 < eta →
    ∃ m : ℝ, 1 < m ∧ ∃ gamma : ℝ, 0 < gamma ∧
      (1+gamma)*(1/m^2) < 1 ∧ areaRatio (1/m^2) gamma < 1+eta)

def CellPerturbationStatement : Prop :=
  ∀ z tau gamma eps : ℝ, ∀ s e : Plane,
    |z| ≤ 1 → s ∈ parameterCell tau → |e.1| ≤ eps → |e.2| ≤ eps →
    eps < 1/2 → eps < gamma*tau/5 →
    ((1+z)*s.1+e.1, (1-z)*s.2+e.2) ∈ interceptCell tau gamma

def GeometryStatement : Prop :=
  CellAreaStatement ∧ CellDilationStatement ∧ CellRatioStatement ∧
    CellParameterStatement ∧ CellPerturbationStatement

end ProductCells

end

end OAI
