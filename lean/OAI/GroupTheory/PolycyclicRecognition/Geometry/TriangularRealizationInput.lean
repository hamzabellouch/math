import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialHeightKernel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieExponential
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

namespace OAI

/-! # Published realization inputs for bounded-height packing

* J. Dixmier, "L'application exponentielle dans les groupes de Lie résolubles",
  Bull. Soc. Math. France 85 (1957), 113–121, Theorem 3, p.120:
  https://www.numdam.org/item/10.24033/bsmf.1483.pdf
  We retain only the global homeomorphism consequence for real triangular
  adjoint action, for the intrinsic exponential.
* A. Onshuus and S. Post, "A definability criterion for connected Lie groups",
  Bull. London Math. Soc. 54 (2022), 449–465, Proposition 2.4 and its proof:
  https://doi.org/10.1112/blms.12574
  https://arxiv.org/html/1910.11287v2#S2
  We retain a positive triangular realization unipotent on the canonical
  nilpotent Lie ideal. That ideal is the nilradical by the already proved
  `kernelIdeal_nilpotent` and `nilpotent_ideal_le_kernelIdeal`. The published
  Lie isomorphism gives the induced topology. Padding a faithful realization
  with a trivial summand allows a positive matrix size, including dimension zero.

The representation is unipotent on the canonical nilpotent Lie ideal.
The resulting height-kernel realization supplies the algebraic data for
bounded-height packing. Definability is not required.
-/

noncomputable section

namespace PolycyclicRecognition

open PositiveTriangular
open scoped Manifold Matrix.Norms.Operator

/-- The global-chart specialization of Dixmier's real-root criterion. -/
def DixmierExponentialInput
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G] : Prop :=
  (∃ a, Nonempty (TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)) →
    (∃ Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G, IsGroupExponential Exp) ∧
    ∀ (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G), IsGroupExponential Exp →
      ∃ chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G, ∀ x, chart x = Exp x

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)

/-- The part of the published triangular realization needed by this proof.
Unipotence is required only for exponentials of the actual canonical ideal. -/
def OnshuusPostRealizationInput [SimplyConnectedSpace G] : Prop :=
  ∀ (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G), IsGroupExponential Exp →
    ∃ m : ℕ, 0 < m ∧ ∃ ρ : G →* positiveTriangular m,
      Topology.IsInducing (fun g => matrix (ρ g)) ∧
      ∀ x ∈ T.kernelIdeal, StrictUpper (matrix (ρ (Exp x)) - 1)

variable [SimplyConnectedSpace G] [IsIsometricSMul G G] [ProperSpace G] [DecidableEq G]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The canonical-height packing property now follows from the precise
published exponential and representation inputs and the proved matrix
packing estimates. No geometric packing premise remains. -/
theorem polynomialBoundedChainPacking_of_published_realization
    (dixmier : DixmierExponentialInput (E := E) (G := G))
    (realize : OnshuusPostRealizationInput T)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (q : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)) :
    PolynomialBoundedChainPacking (fun g => (π g).toAdd) := by
  obtain ⟨chart, hchart⟩ := (dixmier ⟨a, ⟨T⟩⟩).2 Exp hExp
  obtain ⟨m, hm, ρ, hρ, hnil⟩ := realize Exp hExp
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hsurj : Function.Surjective Exp := by
    rw [← show chart = Exp from funext hchart]
    exact chart.surjective
  have hker : ∀ g, π g = 1 → StrictUpper (matrix (ρ g) - 1) := by
    intro g hg
    obtain ⟨x, rfl⟩ := hsurj g
    apply hnil x
    have hp : heightProjection T.character x = 0 := by
      apply q.injective
      rw [map_zero, ← hπExp, hg]
      rfl
    exact (Submodule.Quotient.mk_eq_zero _).mp hp
  exact polynomialBoundedChainPacking_of_unipotent_kernel π ρ
    (integrated_height_surjective T q Exp π hπExp)
    (integrated_height_isQuotientMap T q Exp π hπExp chart (fun x => (hchart x).symm))
    hρ hker

end PolycyclicRecognition

end

end OAI
