import Mathlib
import OAI.Probability.SKGap.Localization.IntegrableLinearCombinationSq
import OAI.Probability.SKGap.Localization.ProdEventSectionLaw

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
namespace SKGapCutoff.Regression

lemma ExponentialEmpiricalConcentration.orthogonal_coefficients
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)] {ρ : ∀ n, Measure (H n)}
    {X : ∀ n, H n → Fin n → E} {ν : Measure E} [IsProbabilityMeasure ν]
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    {r : ℕ} (u : Fin r → E → ℝ) (g : E → ℝ) {K : ℝ≥0}
    (hu : ∀ a, LipschitzWith K (u a)) (hg : LipschitzWith K g)
    (huT : ∀ a, ExponentialSquareTails ρ (fun n h i => u a (X n h i)))
    (hgT : ExponentialSquareTails ρ (fun n h i => g (X n h i)))
    (hui : ∀ a, Integrable (fun x => u a x^2) ν) (hgi : Integrable (fun x => g x^2) ν) :
    ExponentialConvergence ρ (fun n h a => (∑ i, u a (X n h i)*g (X n h i))/(n:ℝ))
      (fun a => ∫ x, u a x*g x ∂ν) := by
  apply ExponentialConvergence.pi_finite
  intro a
  exact hX.product_average (u a) g (hu a) hg (huT a) hgT (hui a) hgi

theorem ExponentialEmpiricalConcentration.normalized_projected_query
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)] {ρ : ∀ n, Measure (H n)}
    {X : ∀ n, H n → Fin n → E} {ν : Measure E} [IsProbabilityMeasure ν]
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    {r : ℕ} (U : ∀ n, H n → Matrix (Fin n) (Fin r) ℝ)
    (u : Fin r → E → ℝ) (g : E → ℝ) {K : ℝ≥0}
    (hu : ∀ a, LipschitzWith K (u a)) (hg : LipschitzWith K g)
    (huT : ∀ a, ExponentialSquareTails ρ (fun n h i => u a (X n h i)))
    (hgT : ExponentialSquareTails ρ (fun n h i => g (X n h i)))
    (hui : ∀ a, Integrable (fun x => u a x^2) ν) (hgi : Integrable (fun x => g x^2) ν)
    (heu : ∀ (n : ℕ) h i a, Real.sqrt n*U n h i a=u a (X n h i))
    (hs : 0 < ∫ x, (residualRecipe u g (fun a => ∫ z, u a z*g z ∂ν) x)^2 ∂ν) :
    let R := fun n h => residualProjection (U n h) *ᵥ (fun i => g (X n h i))
    let s := ∫ x, (residualRecipe u g (fun a => ∫ z, u a z*g z ∂ν) x)^2 ∂ν
    ExponentialConvergence ρ (fun n h => (∑ i, R n h i^2)/(n:ℝ)) s ∧
    ExponentialEmpiricalConcentration ρ
      (fun n h i => (X n h i,Real.sqrt n*unitVector (R n h) i))
      (ν.map (fun x => (x,residualRecipe u g (fun a => ∫ z, u a z*g z ∂ν) x/Real.sqrt s))) ∧
    ExponentialSquareTails ρ (fun n h i => Real.sqrt n*unitVector (R n h) i) := by
  let C := fun n (h : H n) a => (∑ i, u a (X n h i)*g (X n h i))/(n:ℝ)
  let c := fun a => ∫ x, u a x*g x ∂ν
  have hC : ExponentialConvergence ρ C c :=
    hX.orthogonal_coefficients u g hu hg huT hgT hui hgi
  let f : Option (Fin r) → E → ℝ := fun a => a.elim g u
  have hf : ∀ a, LipschitzWith K (f a) := by
    intro a
    cases a with
    | none => exact hg
    | some a => exact hu a
  have hfT : ∀ a, ExponentialSquareTails ρ (fun n h i => f a (X n h i)) := by
    intro a
    cases a with
    | none => exact hgT
    | some a => exact huT a
  have hfi : ∀ a, Integrable (fun x => f a x^2) ν := by
    intro a
    cases a with
    | none => exact hgi
    | some a => exact hui a
  have hsum (b : Fin r → ℝ) (x : E) :
      (∑ a : Option (Fin r), a.elim 1 (fun a => -b a)*f a x)=residualRecipe u g b x := by
    simp [f,Fintype.sum_option,residualRecipe,neg_mul,Finset.sum_neg_distrib,sub_eq_add_neg]
  have hh := hX.normalized_unbounded_linear f hf hfT hfi
    (fun n h (a : Option (Fin r)) => a.elim 1 (fun a => -C n h a))
    (fun a : Option (Fin r) => a.elim 1 (fun a => -c a)) hC.residual_coefficients
    (by simpa only [hsum,c] using hs)
  have hcombo n (h : H n) i :
      (∑ a : Option (Fin r), a.elim 1 (fun a => -C n h a)*f a (X n h i)) =
        (residualProjection (U n h) *ᵥ (fun i => g (X n h i))) i := by
    have hn : 0 < n := Nat.pos_of_ne_zero (fun he => by subst n; exact Fin.elim0 i)
    rw [residual_scaled_predictor hn]
    rw [hsum]
    simp only [heu,C,residualRecipe,mul_comm]
  have hlim x : (∑ a : Option (Fin r), a.elim 1 (fun a => -c a)*f a x)=
      residualRecipe u g c x := hsum c x
  simp_rw [hcombo,hlim] at hh
  dsimp only
  have he n (h : H n) (i : Fin n) : Real.sqrt n*unitVector
      (residualProjection (U n h) *ᵥ (fun j => g (X n h j))) i =
      (residualProjection (U n h) *ᵥ (fun j => g (X n h j))) i /
        Real.sqrt ((∑ j, (residualProjection (U n h) *ᵥ (fun k => g (X n h k))) j^2)/(n:ℝ)) := by
    apply scaled_unitVector
    exact Nat.pos_of_ne_zero (fun hn => by subst n; exact Fin.elim0 i)
  simp only [he]
  exact hh

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise

end

end OAI
