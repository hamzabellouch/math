import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialRepresentationInput
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SupportFlowLegs

namespace OAI

/-! # Support legs in the actual Cartan subgroup

The canonical height section gives a one-parameter subgroup realizing any
height displacement. Its continuity follows from the published faithful
exponential representation, and its height traces the exact affine segment.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra
open scoped Manifold Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)

omit [IsIsometricSMul G G] in
include T hExp in
/-- Continuity of every actual exponential one-parameter subgroup. -/
theorem continuous_exp_line_of_published_realization
    [SimplyConnectedSpace G]
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (x : GroupLieAlgebra (𝓘(ℝ, EG)) G) : Continuous (fun t : ℝ => Exp (t • x)) := by
  obtain ⟨m, hm, ρ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ Exp hExp
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  apply hind.continuous_iff.mpr
  change Continuous (fun t : ℝ => (ρ (Exp (t • x)) : Matrix (Fin m) (Fin m) ℝ))
  simp_rw [hmatch, map_smul]
  exact Units.continuous_val.comp
    (algebraExpUnit_continuous.comp (continuous_id.smul continuous_const))

variable [SimplyConnectedSpace G]
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The actual Cartan direction of a height displacement. -/
def supportLegDirection (w₀ w₁ : W) : H :=
  cartanHeightSection T H (eW.symm (w₁ - w₀))

omit [SimplyConnectedSpace G] [IsIsometricSMul G G] in
theorem supportLegDirection_height (w₀ w₁ : W) :
    eW (heightProjection T.character (supportLegDirection T H eW w₀ w₁)) = w₁ - w₀ := by
  simp [supportLegDirection]

include hExp realize in
/-- An actual one-parameter leg visits the requested height segment with
uniform coarse speed at every scale and on every translated sheet. -/
theorem exists_cartan_support_leg_bound
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    {E : Set W} (hE : Convex ℝ E) {w₀ w₁ : W} (hw₀ : w₀ ∈ E) (hw₁ : w₁ ∈ E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : G) (r : ℝ), 0 ≤ r → (π x).toAdd = r • w₀ →
      let d := fun t : ℝ => Exp (t • (supportLegDirection T H eW w₀ w₁ :
        GroupLieAlgebra (𝓘(ℝ, EG)) G))
      (∀ s t : ℝ, dist (flowLeg d x r s) (flowLeg d x r t) ≤ C * r * |t - s| + C) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ w ∈ E, (π (flowLeg d x r t)).toAdd = r • w) := by
  let v := (supportLegDirection T H eW w₀ w₁ : GroupLieAlgebra (𝓘(ℝ, EG)) G)
  let d := fun t : ℝ => Exp (t • v)
  have hd : Continuous d := continuous_exp_line_of_published_realization T Exp hExp realize v
  obtain ⟨C, hC, hb⟩ := exists_flowLeg_coarse_bound d hd
    (by simp [d, hExp.map_zero]) (fun s t => hExp.map_add_smul v s t)
  refine ⟨C, hC, ?_⟩
  intro x r hr hx
  refine ⟨hb x r hr, ?_⟩
  intro t ht
  apply flowLeg_height_mem π d hE hw₀ hw₁ _ hx ht
  intro u
  simp only [d, hπ, map_smul]
  rw [show eW (heightProjection T.character v) = w₁ - w₀ from
    supportLegDirection_height T H eW w₀ w₁]

end PolycyclicRecognition

end

end OAI
