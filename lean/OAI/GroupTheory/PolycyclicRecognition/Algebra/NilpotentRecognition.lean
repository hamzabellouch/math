import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentChainPacking
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialGrowth
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularHeight

namespace OAI

/-! # The nilpotent comparison branch

A coarse embedding into a simply connected nilpotent Lie group gives
polynomial intrinsic word growth, by the proved nilpotent chain-packing
estimate. The final passage to virtual nilpotence uses exactly Gromov's
published polynomial-growth theorem. This settles the nilpotent branch;
the general solvable height argument remains separate.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold

variable {E G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Group G] [MetricSpace G] [ChartedSpace E G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [MeasurableSpace G] [BorelSpace G] [MeasurableMul G] [IsIsometricSMul G G]
  [ProperSpace G] [SimplyConnectedSpace G]
  [Group H] [MetricSpace H] [IsIsometricSMul H H] [Group.FG H] [DecidableEq H]

/-- The nilpotent branch of recognition, with only the precise published
exponential and polynomial-growth inputs. Surjectivity of the coarse map is
not needed for this branch. -/
theorem virtuallyPolycyclic_of_coarseEmbedding_nilpotent_lieGroup
    (dynkin : NilpotentDynkinExpansionInput E G)
    (haarInput : NilpotentExponentialHaarInput E G)
    (gromov : GromovPolynomialGrowthInput H)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (f : H → G) (hfinite : ∀ R : ℝ, (Metric.closedBall (1 : H) R).Finite)
    {K C K' C' : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hK' : 0 ≤ K')
    (hupper : ∀ x y, dist (f x) (f y) ≤ K * dist x y + C)
    (hlower : ∀ x y, dist x y ≤ K' * dist (f x) (f y) + C') :
    IsVirtuallyPolycyclic H := by
  classical
  obtain ⟨Exp, hExp⟩ := haarInput.1 hnil
  have packing := polynomialBoundedChainPacking_of_nilpotent_exponential dynkin haarInput
    Exp hExp hnil (fun _ : G => (0 : ℝ))
  have hH : Group.IsVirtuallyNilpotent H := virtuallyNilpotent_of_boundedHeight
    gromov f (fun _ : G => (0 : ℝ)) packing hfinite hK hC hK' (le_refl 0)
    hupper hlower (by intro h; simp)
  exact isVirtuallyPolycyclic_of_finitelyGenerated_virtuallyNilpotent H hH

/-- The canonical zero-height branch follows from the triangular adjoint
matrices and Engel's theorem; nilpotence is not an additional premise. -/
theorem virtuallyPolycyclic_of_coarseEmbedding_height_zero
    (dynkin : NilpotentDynkinExpansionInput E G)
    (haarInput : NilpotentExponentialHaarInput E G)
    (gromov : GromovPolynomialGrowthInput H)
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    [Subsingleton (HeightSpace T.character)]
    (f : H → G) (hfinite : ∀ R : ℝ, (Metric.closedBall (1 : H) R).Finite)
    {K C K' C' : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hK' : 0 ≤ K')
    (hupper : ∀ x y, dist (f x) (f y) ≤ K * dist x y + C)
    (hlower : ∀ x y, dist x y ≤ K' * dist (f x) (f y) + C') :
    IsVirtuallyPolycyclic H :=
  virtuallyPolycyclic_of_coarseEmbedding_nilpotent_lieGroup dynkin haarInput gromov
    T.nilpotent_of_height_zero f hfinite hK hC hK' hupper hlower

end PolycyclicRecognition

end

end OAI
