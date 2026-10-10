import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanLeafHeight
import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryGeneratorActionBounds
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxExponents

namespace OAI

/-! # The nilpotent leaf bound from the actual Cartan support data -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Set
open scoped Manifold

variable {EG G W P : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

/-- The positive relation and separation are derived from the actual
unimodular Cartan support datum. Boundary volume comparisons and the
outside-generator quotient actions then give the whole leaf bound. -/
theorem nilpotent_leaf_bound_from_boundary_traces
    (hunimod : ∀ v : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ v) = 0)
    (eW : HeightSpace T.character ≃ₗ[ℝ] W)
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    (ell : Fin M.letterCount → W →ₗ[ℝ] ℝ) (rate : Fin M.letterCount → ℝ)
    (hrate : ∀ i, 0 < rate i)
    (hell : ∀ i, ell i = rate i • (M.supportIn T hunimod eW).weight i)
    (S : Fin M.letterCount → Type*) (act : ∀ i, G →* Equiv.Perm (S i))
    (U : ∀ i, Set (S i)) (η : P → G → W)
    (missing : Fin M.letterCount → Fin M.letterCount)
    (B : Fin M.letterCount → ℝ) (hB : ∀ i, 0 ≤ B i)
    (htrace : ∀ i p x y, act i x '' U i = act i y '' U i →
      |ell i (η p x - η p y)| ≤ B i)
    (hact : ∀ j i, (M.supportIn T hunimod eW).weight i ∉
      positiveWeightRay ((M.supportIn T hunimod eW).weight (missing j)) →
      ∀ t : ℝ, act i (ExpG (t • (M.letter j : GroupLieAlgebra (𝓘(ℝ, EG)) G))) = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p x (n : F.N.carrier),
      ‖η p (x * F.inclusionN n) - η p x‖ ≤ C := by
  let D := M.supportIn T hunimod eW
  obtain ⟨K, hK, hstep⟩ := generator_height_bound_of_boundary_actions
    D.weight ell (fun i => (D.multiplicity γ₀ i : ℝ)) rate
    (fun i => Nat.cast_pos.mpr (D.positive γ₀ i)) hrate
    (D.balanced γ₀) D.separates hell S act U η
    (fun j (t : ℝ) => ExpG (t • (M.letter j : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    missing B hB htrace hact
  exact M.exists_uniform_nilpotent_leaf_bound T F hExpG realize haarN dynkinN b₀ η hK hstep

end PolycyclicRecognition.CartanWordModel

end

end OAI
