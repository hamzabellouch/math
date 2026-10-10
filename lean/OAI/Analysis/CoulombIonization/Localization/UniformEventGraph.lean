import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.QuantumEventMultiplier
import OAI.Analysis.CoulombIonization.FormDomain.LipschitzResidualBase

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace NNReal

namespace CoulombAtom
open CoulombObservation

attribute [local irreducible] graphComponent graphFormVector
  FermionLipschitzMultiplier.apply coulombFormOperator fermionGraph weakGraph
  fermionGraphValue formEnergy energy sectorExcessOperator

lemma FermionLipschitzMultiplier.quantitative_graph_bound {N : ℕ}
    (p : FermionLipschitzMultiplier N) {C : ℝ} (hC : ∀ x, |p.value x| ≤ C)
    (D : Fin N × Fin 3 → ℝ)
    (hD : ∀ i a x, |lineDeriv ℝ p.value x (direction i a)| ≤ D (i,a))
    (F : fermionGraph N) :
    ‖p.apply F‖^2 ≤ (3*C^2+2*(∑ i, ∑ a, D (i,a)^2))*‖F‖^2 := by
  have hm := FermionLipschitzMultiplier.mass_bound (N := N) p hC F
  have hk := FermionLipschitzMultiplier.kinetic_bound (N := N) p hC D hD F
  have hS : 0 ≤ ∑ i : Fin N,∑ a : Fin 3,D (i,a)^2 := by positivity
  have hkin : 0 ≤ ∑ s,∑ i,∑ a,‖graphComponent s (some (i,a)) F‖^2 := by positivity
  exact graph_multiplier_arithmetic (sq_nonneg _) hkin hS hm hk
    (fermionGraph_norm_sq F) (fermionGraph_norm_sq (p.apply F))

def observationGraphFactor (N : ℕ) {J : Type*} [Fintype J] (b : J → ℝ) (p₀ : ℝ) : ℝ :=
  3*((Real.sqrt p₀)⁻¹)^2 + 2*(∑ i : Fin N, ∑ a : Fin 3,
    ((Real.sqrt p₀)⁻¹ *
      ((sqrtLikelihoodLipschitzConstant (I := Fin N × Fin 3) b : ℝ) *
        ‖flattenConfiguration N‖) * ‖direction i a‖)^2)

lemma observationGraphFactor_nonneg (N : ℕ) {J : Type*} [Fintype J]
    (b : J → ℝ) (p₀ : ℝ) : 0 ≤ observationGraphFactor N b p₀ := by
  unfold observationGraphFactor
  positivity

lemma quantumEventMultiplier_uniform_bounds {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (hsy : QuantumEventSymmetric s) {p₀ p : ℝ} (h₀ : 0 < p₀) (hp : p₀ ≤ p) :
    (∀ x, |(quantumEventMultiplier b hs hsy p).value x| ≤ (Real.sqrt p₀)⁻¹) ∧
    ∀ i a x, |lineDeriv ℝ (quantumEventMultiplier b hs hsy p).value x (direction i a)| ≤
      (Real.sqrt p₀)⁻¹ *
        ((sqrtLikelihoodLipschitzConstant (I := Fin N × Fin 3) b : ℝ) *
          ‖flattenConfiguration N‖) * ‖direction i a‖ := by
  have hpinv : (Real.sqrt p)⁻¹ ≤ (Real.sqrt p₀)⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.mpr h₀) (Real.sqrt_le_sqrt hp)
  have hpb : 0 ≤ (Real.sqrt p)⁻¹ := by positivity
  constructor
  · intro x
    rw [quantumEventMultiplier_value,abs_of_nonneg (by positivity)]
    have hx : Real.sqrt (quantumEventLikelihood b s x) ≤ 1 := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (quantumEventLikelihood_le_one b hs x)
    exact (mul_le_of_le_one_right hpb hx).trans hpinv
  · intro i a x
    let m := quantumEventMultiplier b hs hsy p
    have hd : |lineDeriv ℝ m.value x (direction i a)| ≤ (m.constant:ℝ)*‖direction i a‖ := by
      simpa only [Real.norm_eq_abs] using
        (norm_lineDeriv_le_of_lipschitz ℝ m.lipschitz (x₀ := x) (v := direction i a))
    have hc : (m.constant:ℝ) ≤ (Real.sqrt p₀)⁻¹ *
        ((sqrtLikelihoodLipschitzConstant (I := Fin N × Fin 3) b : ℝ)*‖flattenConfiguration N‖) := by
      change ‖(Real.sqrt p)⁻¹‖ *
        ((sqrtLikelihoodLipschitzConstant (I := Fin N × Fin 3) b : ℝ)*‖flattenConfiguration N‖) ≤ _
      rw [Real.norm_of_nonneg hpb]
      exact mul_le_mul_of_nonneg_right hpinv (by positivity)
    exact hd.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

attribute [local irreducible] quantumEventMultiplier

theorem quantumEventMultiplier_uniform_graph {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (hsy : QuantumEventSymmetric s) {p₀ p : ℝ} (h₀ : 0 < p₀) (hp : p₀ ≤ p)
    (F : fermionGraph N) :
    ‖(quantumEventMultiplier b hs hsy p).apply F‖^2 ≤
      observationGraphFactor N b p₀ * ‖F‖^2 := by
  have hd := quantumEventMultiplier_uniform_bounds b hs hsy h₀ hp
  unfold observationGraphFactor
  exact FermionLipschitzMultiplier.quantitative_graph_bound (N := N)
    (quantumEventMultiplier b hs hsy p) hd.1
    (fun ia => (Real.sqrt p₀)⁻¹ *
      ((sqrtLikelihoodLipschitzConstant (I := Fin N × Fin 3) b : ℝ)*‖flattenConfiguration N‖) *
      ‖direction ia.1 ia.2‖) hd.2 F

end CoulombAtom

end

end OAI
