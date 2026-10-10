import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCocycleWordGrowth
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConstructedNilpotentPublishedInputs
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicTriangularRealization
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GeodesicWords

namespace OAI

/-! # Unconditional sublinearity in an actual unimodular Cartan model

The nilpotent models' Haar charts, finite BCH identities and ambient faithful
representation are supplied by their proved constructions.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped Manifold

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (M : CartanWordModel H) (hExp : IsGroupExponential Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
  (hπcont : Continuous (fun g => (π g).toAdd))
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (hρ : ∀ v, Continuous (fun g => ρ g v))
  (hfix : ∀ v, (∀ g, ρ g v = v) → v = 0)

include T F M hExp hunimod hπExp hπcont hρ hfix in
theorem cartan_unitary_cocycle_sublinear
    (b : G → E) (hbc : Continuous b) (hb : IsUnitaryCocycle ρ b)
    {K : Set G} (hK : IsCompact K)
    (length : G → ℝ) (hlen : ∀ g, 0 ≤ length g) {c : ℝ} (hc : 0 ≤ c)
    (hword : ∀ g, ∃ l : List G, (∀ q ∈ l, q ∈ K) ∧ l.prod = g ∧
      (l.length : ℝ) ≤ c * length g + c) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g, ‖b g‖ ≤ ε * length g + B := by
  let nilp := nilpotentPublishedInputs
  have haarN := nilp.haar _ F.N
  have haarD := nilp.haar _ F.D
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := haarD.2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  exact cartan_cocycle_sublinear T F M hExp exponentialLinearRealizationInput_intrinsic
    haarN (nilp.dynkin _ F.N) chartN hchartN chartD hchartD (nilp.dynkin _ F.D)
    hunimod eW π hπExp hπcont ρ hρ hfix b hbc hb hK length hlen hc hword

include T F M hExp hunimod hπExp hπcont hρ hfix in
theorem cartan_unitary_cocycle_sublinear_distance [IsIsometricSMul G G] [ProperSpace G]
    (b : G → E) (hbc : Continuous b) (hb : IsUnitaryCocycle ρ b)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ Set.Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g, ‖b g‖ ≤ ε * dist 1 g + B :=
  cartan_unitary_cocycle_sublinear T F M hExp hunimod eW π hπExp hπcont ρ hρ hfix
    b hbc hb (isCompact_closedBall 1 1) (fun g => dist 1 g) (fun _ => dist_nonneg)
    zero_le_one (by simpa only [one_mul] using wordFactorization_of_minimizing_paths hpath)

end PolycyclicRecognition

end

end OAI
