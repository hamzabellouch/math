import OAI.Analysis.KadisonSimilarity.Tracial.TracialProjectionLifting

namespace OAI

/-! The small-corner estimate passes from coordinate projections to the
actual tracial ultrapower. Norm lifting and compression are constructed. -/

noncomputable section
namespace KadisonSimilarity

open HochschildUltrapower Filter
open scoped ComplexOrder Topology BoundedContinuousFunction

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a * b) = τ (b * a))

/-- An actual lifted projection transfers every coordinate corner bound.
No action of a null algebra sequence on the whole Hilbert ultrapower is asserted. -/
theorem tracialUltrapower_corner_bound_of_projection_lift
    (T : τ.GNS →L[ℂ] τ.GNS) (p : ℕ →ᵇ A) (hp : ∀ i, IsStarProjection (p i))
    (e : Ultrapower τ h1 ω htr) (he : IsStarProjection e)
    (hpe : quotientHom τ h1 ω htr p = e)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcorner : ∀ i, ∀ z : CStarCorner (p i) (hp i),
      ‖commutator T (τ.gnsStarAlgHom (z : A))‖ ≤ ε * ‖z‖)
    (z : CStarCorner e he) :
    ‖commutator (tracialUltrapowerCompression τ h1 ω htr T)
      ((quotientTrace τ h1 ω htr).gnsStarAlgHom (z : Ultrapower τ h1 ω htr))‖ ≤ ε * ‖z‖ := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  let η := δ / (ε + 1)
  have hη : 0 < η := div_pos hδ (by positivity)
  obtain ⟨b, hb, hbn⟩ := HochschildCStarQuotient.norm_mk_lt
    (ideal τ h1 ω htr) (z : Ultrapower τ h1 ω htr) hη
  let a : ℕ →ᵇ A := p * b * p
  have haq : quotientHom τ h1 ω htr a = (z : Ultrapower τ h1 ω htr) := by
    change quotientHom τ h1 ω htr (p * b * p) = _
    have hb' : quotientHom τ h1 ω htr b = (z : Ultrapower τ h1 ω htr) := hb
    rw [map_mul, map_mul, hpe, hb', z.property.1, z.property.2]
  have ha (i : ℕ) : ‖commutator T (τ.gnsStarAlgHom (a i))‖ ≤
      ε * (‖z‖ + η) := by
    let zi : CStarCorner (p i) (hp i) := ⟨a i, by
      change p i * (p i * b i * p i) = p i * b i * p i ∧
        (p i * b i * p i) * p i = p i * b i * p i
      constructor
      · rw [← mul_assoc, ← mul_assoc, (hp i).isIdempotentElem.eq]
      · rw [mul_assoc, (hp i).isIdempotentElem.eq]⟩
    have hpn : ‖p i‖ ≤ 1 := norm_le_one_of_star_projection (p i) (hp i)
    have hzi : ‖zi‖ ≤ ‖z‖ + η := by
      change ‖p i * b i * p i‖ ≤ ‖z‖ + η
      calc
        _ ≤ (‖p i‖ * ‖b i‖) * ‖p i‖ :=
          (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ (1 * ‖b i‖) * 1 := by gcongr
        _ = ‖b i‖ := by ring
        _ ≤ ‖b‖ := b.norm_coe_le_norm i
        _ ≤ ‖z‖ + η := hbn.le
    exact (hcorner i zi).trans (mul_le_mul_of_nonneg_left hzi hε)
  have hbnd := norm_tracialUltrapowerCompression_commutator_le τ h1 ω htr T a
    (mul_nonneg hε (by positivity : 0 ≤ ‖z‖ + η))
    (Filter.Eventually.of_forall ha)
  rw [haq] at hbnd
  have hcancel : η * (ε + 1) = δ := div_mul_cancel₀ δ (by positivity)
  nlinarith [hη]

end KadisonSimilarity

end

end OAI
