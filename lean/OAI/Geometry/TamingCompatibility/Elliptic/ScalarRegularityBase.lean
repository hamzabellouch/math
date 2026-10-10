import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.MemSobolevSum
import OAI.Geometry.TamingCompatibility.Functional.GeometricCompact
import OAI.Geometry.TamingCompatibility.DifferentialForms.ScalarJet

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart MeasureTheory
open EuclideanSobolevOperators TemperedDistribution
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def scalarDistribution (p : A.centers) : antiEnergy A J α hs ht →L[ℝ] 𝓢'(Space,ScalarPair.F) :=
  ScalarPair.jetDistribution none ∘L energyToScalarJet A J α hs ht D hD p

lemma scalarDistribution_H1 (p : A.centers) (u : antiEnergy A J α hs ht) :
    MemSobolev 1 2 (scalarDistribution A J α hs ht D hD p u) := by
  have h0 (j : DerivativeIndex) : MemSobolev 0 2
      (ScalarPair.jetDistribution j (energyToScalarJet A J α hs ht D hD p u)) := by
    refine ⟨energyToScalarJet A J α hs ht D hD p u j,?_⟩
    simp only [besselPotential_zero,ContinuousLinearMap.id_apply]
    rfl
  have hd (i : Fin (Module.finrank ℝ Space)) : MemSobolev 0 2
      (LineDeriv.lineDerivOpCLM ℝ 𝓢'(Space,ScalarPair.F) (stdOrthonormalBasis ℝ Space i)
        (scalarDistribution A J α hs ht D hD p u)) := by
    change MemSobolev 0 2 (LineDeriv.lineDerivOpCLM ℝ _ _
      (ScalarPair.jetDistribution none (energyToScalarJet A J α hs ht D hD p u)))
    rw [energy_scalar_derivative]
    exact h0 (some i)
  convert memSobolev_succ_of_derivatives (stdOrthonormalBasis ℝ Space) (h0 none) hd using 1
  · norm_num
  · rfl

lemma weak_equation_transpose (u : antiEnergy A J α hs ht) (f : L2 A J α hs ht true)
    (h : ∀ v : antiEnergy A J α hs ht,
      ⟪weakDelta A J α hs ht u,weakDelta A J α hs ht v⟫ =
        ⟪f,energyInclusion A J α hs ht v⟫)
    (a : antiPre A J α hs ht) :
    ⟪energyInclusion A J α hs ht u,testDerivative A J α hs ht (antiDelta A J α hs ht a)⟫ =
      ⟪f,smoothL2 A J α hs ht true a.val⟫ := by
  have hw := antiEnergy_weak A J α hs ht u (antiDelta A J α hs ht a)
  have he := h (antiToEnergy A J α hs ht a)
  change ⟪weakDelta A J α hs ht u,smoothL2 A J α hs ht false (antiDelta A J α hs ht a)⟫ = _ at he
  change ⟪testDerivative A J α hs ht (antiDelta A J α hs ht a),energyInclusion A J α hs ht u⟫ =
    ⟪smoothL2 A J α hs ht false (antiDelta A J α hs ht a),weakDelta A J α hs ht u⟫ at hw
  rw [real_inner_comm,hw,real_inner_comm]
  exact he

end TamingCompatibility.GeometricHilbert

end

end OAI
