import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialRepeatedWords
import OAI.Analysis.KadisonSimilarity.Tracial.TracialBaseSpace

namespace OAI

/-! Propagation on the entire base Hilbert space. Polar decomposition is used
only for the right support of the bounded vector qv; density handles all other
base vectors. The full-column bound is derived from the cited cyclic inputs. -/

noncomputable section
namespace KadisonSimilarity

universe u v
variable {P : Type u} {H : Type v} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The application-specific consequence of support projections and polar
 decomposition (Blackadar, I.5.2.1--3): the right support of qv has trace at most
that of its containing left projection q. -/
def TracialRightSupportInput (τ : P → ℝ) (q : P) (A : StarSubalgebra ℂ P) : Prop :=
  ∀ v : A, ∃ r : P, IsStarProjection r ∧ τ r ≤ τ q ∧ (q * (v : P)) * r = q * (v : P)

variable {D E F V : Type*} [CStarAlgebra D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {GD : TracialCornerGeometry D E} {G : TracialCornerGeometry P H}
  {ι : D →⋆ₐ[ℂ] P} {W : TracialHeadCoordinates GD G ι F}
  [W.vacuum.HasOrthogonalProjection]
  {q : D} {hq : IsStarProjection q} {z : unitary (CStarCorner q hq)} {a : ℝ}
  {Y : H →L[ℂ] H} {A : StarSubalgebra ℂ P}
  {B₀ : G.baseSpace A →L[ℂ] G.baseSpace A} {Bₖ : V →L[ℂ] V}

namespace TracialRepeatedWordRealization

/-- A supported full-column estimate on each bounded base vector propagates
to every vector of the actual closed base space. The support may depend on v. -/
theorem propagation_on_base
    (R : TracialRepeatedWordRealization W z a Y B₀ Bₖ)
    (hτ : GD.trace 1 = 1) (ha : 0 < a)
    (htrace : GD.trace q = (a : ℂ)) (hhaar : HaarCornerMoments GD.trace z a)
    (τ : P → ℝ) (support : TracialRightSupportInput τ (ι q) A)
    (hsmall : ∀ v : A, R.small (G.baseVector A v) = G.vector (ι q * (v : P)))
    {η : ℝ}
    (hcolumn : ∀ r : P, IsStarProjection r → τ r ≤ τ (ι q) →
      ∃ b : P, r * b = b ∧
        ‖(Y - G.right b).comp (G.corner 1 r).toSubmodule.subtypeL‖ ≤ η)
    (v : G.baseSpace A) :
    ‖Bₖ (R.repeatVector v) - R.repeatVector (B₀ v)‖ ≤ 2 * η * ‖v‖ := by
  refine (G.baseVector_dense A).induction_on v (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro v
  obtain ⟨r, hr, htr, hvr⟩ := support v
  obtain ⟨b, _, hb⟩ := hcolumn r hr htr
  have hv : R.small (G.baseVector A v) ∈ (G.corner 1 r).toSubmodule := by
    rw [hsmall]
    change G.vector (ι q * (v : P)) ∈ G.corner 1 r
    rw [G.mem_corner]
    exact ⟨by simp, by simp only [G.right_vector, hvr]⟩
  exact R.propagation hτ ha htrace hhaar r b hb _ hv

/-- All full-column assumptions are discharged using the actual matrix frame
and published cyclic implementation and tracial commutation inputs. -/
theorem propagation_on_base_of_published_inputs
    (R : TracialRepeatedWordRealization W z a Y B₀ Bₖ)
    (hτ : GD.trace 1 = 1) (ha : 0 < a)
    (htrace : GD.trace q = (a : ℂ)) (hhaar : HaarCornerMoments GD.trace z a)
    (τ : P → ℝ) (support : TracialRightSupportInput τ (ι q) A)
    (hsmall : ∀ v : A, R.small (G.baseVector A v) = G.vector (ι q * (v : P)))
    (e : P) (he : IsStarProjection e) (hqe : τ (ι q) ≤ τ e)
    (hfaithful : Function.Injective G.vector)
    (comparison : FiniteFactorProjectionComparison τ)
    {n : ℕ} (hn : 0 < n) (frame : Fin n → P)
    (hframe : ∀ i j, star (frame i) * frame j = if i = j then e else 0)
    (hsum : ∑ i, frame i * star (frame i) = 1)
    (hYe : Y.comp (G.left e) = (G.left e).comp Y)
    (hYframe : ∀ i, Y.comp (G.left (frame i)) = (G.left (frame i)).comp Y)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hY : ∀ x : CStarCorner e he, ‖commutator Y (G.left (x : P))‖ ≤ ε * ‖x‖)
    (published : PublishedDerivationInputs.{u,v} (CStarCorner e he))
    (commutation : TracialCommutationInput G.left (G.faithfulRightAction hfaithful))
    (v : G.baseSpace A) :
    ‖Bₖ (R.repeatVector v) - R.repeatVector (B₀ v)‖ ≤
      2 * cyclicConstant * ε * ‖v‖ := by
  have hp := R.propagation_on_base hτ ha htrace hhaar τ support hsmall
    (fun r hr htr => G.full_column e he r hfaithful τ comparison hr (htr.trans hqe)
      hn frame hframe hsum Y hYe hYframe hε hY published commutation) v
  simpa only [cyclicConstant, rowConstant, mul_assoc] using hp

end TracialRepeatedWordRealization
end KadisonSimilarity

end

end OAI
