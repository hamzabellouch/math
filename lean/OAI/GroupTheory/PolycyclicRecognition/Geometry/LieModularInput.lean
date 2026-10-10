import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieModelUnimodular
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieExponential
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Analysis.Complex.Exponential

namespace OAI

/-!
# From right Haar invariance to zero adjoint trace

The sole input is the scalar modular formula on one-parameter subgroups.
It is the combination of A. W. Knapp, *Lie Groups Beyond an Introduction*,
second edition, Progress in Mathematics 140, Birkhäuser (2002):
Proposition 8.27, pp.532–533 (the modular determinant), Proposition 1.91
and equation (1.92), p.80 (the adjoint exponential), and Proposition
0.11(e), p.7 (the determinant of an exponential). The author's digital
second edition (2023) explicitly preserves pp.1–812 of the printed edition:
https://www.math.stonybrook.edu/~aknapp/download/Beyond2.pdf

Knapp's convention in (8.26) agrees with the pushforward convention of
`Measure.modularCharacter`. No vanishing trace conclusion is an input.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory LieAlgebra
open scoped Manifold

/-- Right invariance makes the actual modular character identically one. -/
theorem modularCharacter_eq_one_of_rightInvariant
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (g : G) :
    Measure.modularCharacter g = 1 := by
  change Measure.modularCharacterFun g = 1
  simpa only [map_mul_right_eq_self, Measure.haarScalarFactor_self] using
    Measure.modularCharacterFun_eq_haarScalarFactor μ g

section LieGroup

/-- The scalar specialization of Knapp's modular and exponential
identities, for the intrinsic exponential characterized in this project. -/
def LieModularExponentialInput (E G : Type*)
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SecondCountableTopology G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] : Prop :=
  ∀ (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G), IsGroupExponential Exp →
    ∀ x : GroupLieAlgebra (𝓘(ℝ, E)) G,
      (Measure.modularCharacter (Exp x) : ℝ) =
        Real.exp (LinearMap.trace ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G) (ad ℝ _ x))

variable {E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SecondCountableTopology G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- Haar right invariance and the published scalar identity imply the
precise adjoint trace condition used by the Cartan box development. -/
theorem trace_ad_eq_zero_of_isMulRightInvariant
    (modularInput : LieModularExponentialInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    LinearMap.trace ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G) (ad ℝ _ x) = 0 := by
  apply (Real.exp_eq_one_iff _).mp
  rw [← modularInput Exp hExp x, modularCharacter_eq_one_of_rightInvariant μ]
  rfl

end LieGroup

/-- The trace condition for a Lie model follows from the original uniform
lattice comparison; unimodularity is obtained by metric Følner transfer. -/
theorem SimplyConnectedSolvableLieModel.trace_ad_eq_zero_of_lattice_comparison
    (fw : FarbWeinbergerLatticeInput) (S T : SimplyConnectedSolvableLieModel)
    (Λ : Subgroup S.carrier) (hΛ : IsUniformLattice Λ)
    (dS : ProperChainMetric S.carrier) (dT : ProperChainMetric T.carrier)
    (e : letI := dS.compatibleMetric
      letI := dT.compatibleMetric
      MetricQuasiEquivalence S.carrier T.carrier)
    (modularInput :
      letI : IsTopologicalGroup T.carrier :=
        topologicalGroup_of_lieGroup (𝓘(ℝ, T.modelSpace)) ⊤
      letI : LocallyCompactSpace T.carrier :=
        Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, T.modelSpace))
      LieModularExponentialInput T.modelSpace T.carrier)
    (Exp : GroupLieAlgebra (𝓘(ℝ, T.modelSpace)) T.carrier → T.carrier)
    (hExp : IsGroupExponential Exp)
    [MeasurableSpace T.carrier] [BorelSpace T.carrier]
    (μ : Measure T.carrier) [μ.IsHaarMeasure] [Measure.InnerRegular μ]
    (x : GroupLieAlgebra (𝓘(ℝ, T.modelSpace)) T.carrier) :
    LinearMap.trace ℝ (GroupLieAlgebra (𝓘(ℝ, T.modelSpace)) T.carrier) (ad ℝ _ x) = 0 := by
  let : IsTopologicalGroup T.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, T.modelSpace)) ⊤
  let : LocallyCompactSpace T.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, T.modelSpace))
  let : μ.IsMulRightInvariant :=
    SimplyConnectedSolvableLieModel.isMulRightInvariant_of_lattice_comparison
      fw S T Λ hΛ dS dT e μ
  exact trace_ad_eq_zero_of_isMulRightInvariant modularInput Exp hExp μ x

end PolycyclicRecognition

end

end OAI
