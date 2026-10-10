import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildHeatForm

namespace OAI

/-! Scalar interpretation of the effective source and initial value. -/

noncomputable section
namespace ForcedComputation.PlaneScalarMild

open Set ShearFlows MeasureTheory
open scoped Topology Interval BigOperators BoundedContinuousFunction

private def scalarPathEvaluation {T : ℝ} (k : ℕ) (t : Icc (0 : ℝ) T) (x : Plane) :
    WeaklySingular.Path (Jet k) T →L[ℝ] ℝ :=
  (BoundedContinuousFunction.evalCLM ℝ x).comp
    ((BoundedSpatialJets.functionMap Plane ℝ k).comp
      ((ContinuousMap.evalCLM ℝ t).comp
        (WeaklySingular.pathEquiv (Jet k) T).toContinuousLinearEquiv.toContinuousLinearMap))

@[simp] private theorem scalarPathEvaluation_apply {T : ℝ} (k : ℕ)
    (t : Icc (0 : ℝ) T) (x : Plane) (u : WeaklySingular.Path (Jet k) T) :
    scalarPathEvaluation k t x u = BoundedSpatialJets.function Plane ℝ k (u t) x := rfl

namespace CompatibleData

theorem solutionJet_function {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (k : ℕ) (t : Icc (0 : ℝ) T) (x : Plane) :
    BoundedSpatialJets.function Plane ℝ k (D.solutionJet hT hν k t) x = D.solution hT hν t x :=
  (commonFunction_eq hT hν D.coefficient (D.affinePath hT hν)
    D.coefficient_truncate (D.affinePath_truncate hT hν) k t x).symm

/-- The represented derivative of a coefficient product is the actual spatial derivative. -/
private theorem product_directional_function {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (b : Fin 3 → ℝ × Plane → ℝ)
    (hb : ∀ k i t x, BoundedSpatialJets.function Plane ℝ k (D.coefficient k i t) x = b i (t.val,x))
    (k : ℕ) (i : Fin 3) (v : Plane) (t : Icc (0 : ℝ) T) (x : Plane) :
    scalarPathEvaluation k t x (directionalPath k v T
      (productPath (k+1) (D.coefficient (k+1) i) (D.solutionJet hT hν (k+1)))) =
      fderiv ℝ (fun y => b i (t.val,y) * D.solution hT hν t y) x v := by
  change BoundedSpatialJets.function Plane ℝ k
    (BoundedSpatialJets.directionalDerivativeCLM Plane ℝ k v
      (multiplication (k+1) (D.coefficient (k+1) i t) (D.solutionJet hT hν (k+1) t))) x = _
  rw [BoundedSpatialJets.function_directionalDerivativeCLM]
  have he : (BoundedSpatialJets.function Plane ℝ (k+1)
      (multiplication (k+1) (D.coefficient (k+1) i t) (D.solutionJet hT hν (k+1) t)) : Plane → ℝ) =
      (fun y => b i (t.val,y) * D.solution hT hν t y) := by
    funext y
    rw [multiplication_apply, hb, D.solutionJet_function]
  rw [he]

/-- The Banach-space effective source has the expected divergence-form scalar value. -/
theorem effectiveSource_function {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (h : ℝ × Plane → ℝ) (b : Fin 3 → ℝ × Plane → ℝ)
    (hh : ∀ k t x, BoundedSpatialJets.function Plane ℝ k (D.source k t) x = h (t.val,x))
    (hb : ∀ k i t x, BoundedSpatialJets.function Plane ℝ k (D.coefficient k i t) x = b i (t.val,x))
    (k : ℕ) (t : Icc (0 : ℝ) T) (x : Plane) :
    BoundedSpatialJets.function Plane ℝ k (D.effectiveSource hT hν k t) x =
      h (t.val,x) + b 0 (t.val,x) * D.solution hT hν t x +
        ∑ j : Fin 2, fderiv ℝ (fun y => b j.succ (t.val,y) * D.solution hT hν t y) x
          (Pi.single j 1) := by
  change scalarPathEvaluation k t x (D.source k +
    productPath k (D.coefficient k 0) (D.solutionJet hT hν k) +
    ∑ j : Fin 2, directionalPath k (Pi.single j 1) T
      (productPath (k+1) (D.coefficient (k+1) j.succ) (D.solutionJet hT hν (k+1)))) = _
  rw [map_add, map_add, map_sum]
  simp only [scalarPathEvaluation_apply, productPath_apply, multiplication_apply, hh, hb,
    D.solutionJet_function]
  exact congrArg (fun z : ℝ => h (t.val,x) + b 0 (t.val,x) * D.solution hT hν t x + z)
    (Finset.sum_congr rfl (fun j _ => D.product_directional_function hT hν b hb k j.succ
      (Pi.single j 1) t x))

/-- The mild solution takes exactly its prescribed initial value. -/
theorem solution_initial {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (x : Plane) :
    D.solution hT hν ⟨0, le_rfl, hT⟩ x = BoundedSpatialJets.function Plane ℝ 0 (D.initial 0) x := by
  let t₀ : Icc (0 : ℝ) T := ⟨0, le_rfl, hT⟩
  have he := congrArg (fun u : WeaklySingular.Path (Jet 0) T => u t₀)
    (D.solutionJet_heat_form hT hν 0)
  change D.solutionJet hT hν 0 t₀ = initialHeatPath hν 0 (D.initial 1) t₀ +
    heatSourcePath hT hν 0 (D.effectiveSource hT hν 0) t₀ at he
  rw [initialHeatPath_apply, heatSourcePath_apply] at he
  simp only [t₀, mul_zero, PlaneHeat.evolutionOperator_initial, ContinuousLinearMap.id_apply,
    intervalIntegral.integral_same, add_zero] at he
  have hJ := D.initial_truncate 0 1 (by omega)
  have hs := congrArg (fun J : Jet 0 => BoundedSpatialJets.function Plane ℝ 0 J x) (he.trans hJ)
  exact (D.solutionJet_function hT hν 0 t₀ x).symm.trans hs

end CompatibleData
end ForcedComputation.PlaneScalarMild

end

end OAI
