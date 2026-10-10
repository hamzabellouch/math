import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialRepresentationInput
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RootRepresentation

namespace OAI

/-! # Actual root distortion from the published linear realization

All contraction, continuity, and conjugation premises of the root-space
distortion theorem are now discharged for the ambient Lie group. Only the
already recorded faithful exponential-realization input remains assumed.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule
open scoped Manifold Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] rootNormedAddCommGroup rootNormedSpace rootNontrivial

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]

/-- Every actual nonzero Cartan root space is logarithmically distorted
in the ambient metric. -/
theorem root_distortion_of_published_realization
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
    (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
    (χ : Weight ℝ H (GroupLieAlgebra (𝓘(ℝ, EG)) G)) (hχ : χ.IsNonZero)
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G)) :
    ∃ D : ℝ, 0 < D ∧ ∀ v : rootSpace H χ,
      dist 1 (Exp v) ≤ D * Real.log (2 + ‖(rootCoordinates H χ) v‖) := by
  let : TopologicalSpace (rootSpace H χ) :=
    (rootNormedAddCommGroup H χ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  obtain ⟨m, hm, ρ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ Exp hExp
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  obtain ⟨h, hh⟩ := exists_contracting_root_direction H χ hχ
  let d : ℝ → G := fun t => Exp (-(t • (h : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
  have hEr : Continuous (fun v : rootSpace H χ => Exp v) := by
    apply hind.continuous_iff.mpr
    change Continuous (fun v : rootSpace H χ => (ρ (Exp v) : Matrix (Fin m) (Fin m) ℝ))
    simp_rw [hmatch]
    exact Units.continuous_val.comp
      (algebraExpUnit_continuous.comp (representedRootVector H χ j).continuous)
  have hd : Continuous d := by
    apply hind.continuous_iff.mpr
    change Continuous (fun t : ℝ => (ρ (Exp (-(t • (h : GroupLieAlgebra (𝓘(ℝ, EG)) G)))) :
      Matrix (Fin m) (Fin m) ℝ))
    simp_rw [hmatch, map_neg, map_smul]
    exact Units.continuous_val.comp (algebraExpUnit_continuous.comp
      (continuous_id.smul continuous_const).neg)
  exact represented_root_logarithmic_distortion H χ j ρ hρ
    (fun v => Exp v) hEr h hh d hd (fun v => hmatch v)
    (fun t => by simp only [d, hmatch, map_neg, map_smul])

end PolycyclicRecognition

end

end OAI
