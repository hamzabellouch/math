import OAI.Analysis.IrrationalRotation.Product.ProductOrbitPair
import OAI.Analysis.IrrationalRotation.Product.ProductPairTransfer

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.ProductModel

theorem exists_covariantProjectionField_pairIdentity
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (hsampling : HasAllFiniteCoordinateSampling θ)
    (p : Hilbert →L[ℂ] Hilbert) (hpM : p ∈ factor θ) (hp : IsStarProjection p)
    (hinv : (1 - p) * weightedOperator θ c * p = 0) :
    ∃ F : Base → Fiber →L[ℂ] Fiber,
      IsCovariantFieldRepresentation θ p F 1 ∧
      (∀ x, IsStarProjection (F x)) ∧
      ∀ I : Finset ℕ, ∀ᵐ xy ∂triangularLaw I, PairIdentity θ c F xy := by
  obtain ⟨F, hF, hproj⟩ := exists_covariantProjectionField hpM hp
  refine ⟨F, hF, hproj, ?_⟩
  intro I
  apply pairIdentity_of_orderedOrbitSampling θ c hθ0 hθ hc F hproj hF.2.2.1
    _ I (hsampling I)
  intro n _hn
  exact (ae_orbit_pair_identity θ c hθ0 hc hθ p hpM F hproj hF.2.2.2.1 hinv n).mono
    (fun _ hx _ => hx)

end Invariant233.ProductModel

end

end OAI
