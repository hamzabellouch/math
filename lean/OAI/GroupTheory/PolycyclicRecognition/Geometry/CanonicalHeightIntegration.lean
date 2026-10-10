import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularRealizationInput
import OAI.GroupTheory.PolycyclicRecognition.Geometry.HeightLipschitz

namespace OAI

/-!
# Integrating the canonical height

J. M. Lee, *Introduction to Smooth Manifolds*, second edition, GTM 218,
Springer (2013), Theorem 20.19, p.530, integrates a Lie algebra homomorphism
from a simply connected group. Proposition 20.8(g), p.520, gives compatibility
with the exponential. We retain just the real-valued character specialization:
a real linear form vanishing on brackets integrates to a continuous additive
character. This is the same published integration theorem as in
`NilpotentLieIntegrationInput`, with an arbitrary simply connected source and
the one-dimensional abelian target. No height quotient, Lipschitz bound or
recognition conclusion is assumed in this input.

The diagonal characters are already proved to kill brackets. Integrating them
and using the existing global exponential chart constructs the actual height
homomorphism. Its continuity, surjectivity, quotient property and global
Lipschitz bound are then proved.

Primary text: https://math.berkeley.edu/~jchaidez/materials/reu/lee_smooth_manifolds.pdf
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold

section Topological

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

/-- The scalar-target specialization of Lee 20.19 and 20.8(g). -/
def ScalarCharacterIntegrationInput [T2Space G] [SecondCountableTopology G] : Prop :=
  SimplyConnectedSpace G →
    ∀ ℓ : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ[ℝ] ℝ,
      (∀ x y : GroupLieAlgebra (𝓘(ℝ, E)) G, ℓ ⁅x, y⁆ = 0) →
      ∀ (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G), IsGroupExponential Exp →
        ∃ c : G →* Multiplicative ℝ, Continuous (fun g => (c g).toAdd) ∧
          ∀ x, (c (Exp x)).toAdd = ℓ x

variable [T2Space G] [SecondCountableTopology G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Integrated scalar characters make the logarithmic quotient formula into
an actual continuous group homomorphism. No group law for the logarithm is
assumed. -/
theorem exists_canonical_height_of_exponential_chart
    (integrate : ScalarCharacterIntegrationInput (E := E) (G := G))
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (e : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (he : ∀ x, e x = Exp x) :
    ∃ π : G →* Multiplicative W,
      Continuous (fun g => (π g).toAdd) ∧
      (∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)) ∧
      Function.Surjective π ∧ Topology.IsQuotientMap (fun g => (π g).toAdd) := by
  choose c _hc hcExp using fun i =>
    integrate inferInstance (T.character i) (T.character_lie i) Exp hExp
  have hc (i : Fin a) (g : G) :
      T.character i (e.symm g) = (c i g).toAdd := by
    rw [← hcExp i, ← he, e.apply_symm_apply]
  have hzero : heightProjection T.character (e.symm 1) = 0 := by
    apply heightCharacters_separate T.character
    intro i
    rw [heightCharacter_projection, hc, map_one]
    rfl
  have hmul (g h : G) : heightProjection T.character (e.symm (g * h)) =
      heightProjection T.character (e.symm g) + heightProjection T.character (e.symm h) := by
    apply sub_eq_zero.mp
    apply heightCharacters_separate T.character
    intro i
    simp only [map_sub, map_add, heightCharacter_projection, hc, map_mul, toAdd_mul]
    abel
  let π : G →* Multiplicative W :=
    { toFun := fun g => Multiplicative.ofAdd (q (heightProjection T.character (e.symm g)))
      map_one' := by
        apply Multiplicative.ext
        change q (heightProjection T.character (e.symm 1)) = 0
        rw [hzero, map_zero]
      map_mul' := by
        intro g h
        apply Multiplicative.ext
        change q (heightProjection T.character (e.symm (g * h))) =
          q (heightProjection T.character (e.symm g)) + q (heightProjection T.character (e.symm h))
        rw [hmul, map_add] }
  have hπExp (x) : (π (Exp x)).toAdd = q (heightProjection T.character x) := by
    change q (heightProjection T.character (e.symm (Exp x))) = _
    rw [← he, e.symm_apply_apply]
  refine ⟨π, ?_, hπExp, integrated_height_surjective T q Exp π hπExp,
    integrated_height_isQuotientMap T q Exp π hπExp e (fun x => (he x).symm)⟩
  exact ((q.toLinearMap.comp (heightProjection T.character)).continuous_of_finiteDimensional).comp
    e.symm.continuous

end Topological

section Metric

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]
  [SecondCountableTopology G] [IsIsometricSMul G G] [ProperSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The published scalar integration and global exponential inputs supply
the actual canonical height with all metric compatibility hypotheses used by
the transferred-height argument. -/
theorem exists_lipschitz_canonical_height
    (chains : LinearMetricChains G)
    (integrate : ScalarCharacterIntegrationInput (E := E) (G := G))
    (dixmier : DixmierExponentialInput (E := E) (G := G))
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp) :
    ∃ π : G →* Multiplicative W,
      (∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)) ∧
      Function.Surjective π ∧ Topology.IsQuotientMap (fun g => (π g).toAdd) ∧
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y := by
  obtain ⟨e, he⟩ := (dixmier ⟨a, ⟨T⟩⟩).2 Exp hExp
  obtain ⟨π, hπ, hπExp, hsurj, hquot⟩ :=
    exists_canonical_height_of_exponential_chart T integrate q Exp hExp e he
  exact ⟨π, hπExp, hsurj, hquot, continuous_height_lipschitz chains π hπ⟩

end Metric

end PolycyclicRecognition

end

end OAI
