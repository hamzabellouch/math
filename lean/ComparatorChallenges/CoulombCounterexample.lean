import Mathlib

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

abbrev E3 := EuclideanSpace ℝ (Fin 3)

abbrev Triple := E3 × (E3 × E3)

def tripleFst (t : Triple) : E3 := t.1

def tripleSnd (t : Triple) : E3 := t.2.1

def tripleThd (t : Triple) : E3 := t.2.2

def invDistance (x y : E3) : ℝ≥0∞ :=
  (ENNReal.ofReal ‖x - y‖)⁻¹

def coulombCost (t : Triple) : ℝ≥0∞ :=
  invDistance (tripleFst t) (tripleSnd t) +
    invDistance (tripleFst t) (tripleThd t) +
    invDistance (tripleSnd t) (tripleThd t)

def IsThreeCoupling (mu : Measure E3) (pi : Measure Triple) : Prop :=
  IsProbabilityMeasure pi ∧
    Measure.map tripleFst pi = mu ∧
    Measure.map tripleSnd pi = mu ∧
    Measure.map tripleThd pi = mu

def densityMeasure (rho : E3 → ℝ) : Measure E3 :=
  Measure.withDensity (volume : Measure E3) (fun x => ENNReal.ofReal (rho x))

def Preserves (mu : Measure E3) (T : E3 → E3) : Prop :=
  Measurable T ∧ Measure.map T mu = mu

def graphCost (mu : Measure E3) (T2 T3 : E3 → E3) : ℝ≥0∞ :=
  ∫⁻ x, coulombCost (x, (T2 x, T3 x)) ∂mu

def kantorovichValue (mu : Measure E3) : ℝ≥0∞ :=
  ⨅ (pi : Measure Triple), ⨅ (_h : IsThreeCoupling mu pi),
    ∫⁻ t, coulombCost t ∂pi

def mongeValue (mu : Measure E3) : ℝ≥0∞ :=
  ⨅ (T2 : E3 → E3), ⨅ (T3 : E3 → E3),
    ⨅ (_h2 : Preserves mu T2), ⨅ (_h3 : Preserves mu T3),
      graphCost mu T2 T3

def IsSmoothCompactProbabilityDensity (rho : E3 → ℝ) : Prop :=
  (∀ x, 0 ≤ rho x) ∧
    ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) rho ∧
    HasCompactSupport rho ∧
    ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) (fun x : E3 => Real.sqrt (rho x)) ∧
    HasCompactSupport (fun x : E3 => Real.sqrt (rho x)) ∧
    (∫ x : E3, rho x ∂(volume : Measure E3)) = 1

def KantorovichAttained (mu : Measure E3) : Prop :=
  ∃ pi : Measure Triple,
    IsThreeCoupling mu pi ∧
      (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu

def NoMongeOptimizer (mu : Measure E3) : Prop :=
  ∀ T2 T3 : E3 → E3,
    Preserves mu T2 → Preserves mu T3 →
      kantorovichValue mu < graphCost mu T2 T3

def FiniteMongeApproximation (mu : Measure E3) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ T2 T3 : E3 → E3,
      Preserves mu T2 ∧
      Preserves mu T3 ∧
      graphCost mu T2 T3 < ⊤ ∧
      graphCost mu T2 T3 ≤
        kantorovichValue mu + ENNReal.ofReal epsilon

def HasCoulombCounterexample (rho : E3 → ℝ) : Prop :=
  IsSmoothCompactProbabilityDensity rho ∧
    IsProbabilityMeasure (densityMeasure rho) ∧
    kantorovichValue (densityMeasure rho) < ⊤ ∧
    KantorovichAttained (densityMeasure rho) ∧
    NoMongeOptimizer (densityMeasure rho)

def HasFullCoulombConclusion (rho : E3 → ℝ) : Prop :=
  HasCoulombCounterexample rho ∧
    mongeValue (densityMeasure rho) =
      kantorovichValue (densityMeasure rho) ∧
    FiniteMongeApproximation (densityMeasure rho)

theorem coulomb_counterexample_and_equal_infima :
    ∃ rho : E3 → ℝ, HasFullCoulombConclusion rho := by
  sorry

end Problem356

end

end OAI
