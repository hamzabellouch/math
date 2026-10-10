import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSourceDilation

namespace OAI

/-! # Identifying the source dilation from its exponential formula -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

/-- Exponential surjectivity identifies a source automorphism with the
canonical continuous dilation, without an extra compatibility hypothesis. -/
theorem sourceDilation_eq_of_exp
    (hbij : Function.Bijective F.ExpN)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (h : H) (S : F.N.carrier ≃ₜ* F.N.carrier)
    (hS : ∀ v, S (F.ExpN (F.N.equiv v)) =
      F.ExpN (F.N.equiv (cartanIdealWeightDilation T H h v))) :
    S = M.sourceDilation T F hbij chartN hchartN dynkinN h := by
  ext z
  obtain ⟨v, rfl⟩ := hbij.surjective z
  obtain ⟨v, rfl⟩ := F.N.equiv.surjective v
  exact (hS v).trans (M.sourceDilation_apply_exp T F hbij chartN hchartN dynkinN h v).symm

end PolycyclicRecognition.CartanWordModel

end

end OAI
