import OAI.Analysis.KadisonSimilarity.Tracial.MatrixCornerFrames
import OAI.Analysis.KadisonSimilarity.Tracial.FullColumnTheorem
import OAI.Analysis.KadisonSimilarity.Representation.CStarCorner

namespace OAI

/-! A small-corner commutator estimate transports along a partial isometry
in the algebra commuting with the implementing operator. Projection
comparison then supplies that partial isometry in the prescribed factor. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

/-- A partial isometry is contractive, including when its initial projection
is zero. -/
theorem norm_le_one_of_initial_projection (v f : P) (hf : IsStarProjection f)
    (hv : star v * v = f) : ‖v‖ ≤ 1 := by
  have hfn : ‖f‖ * ‖f‖ = ‖f‖ := by
    rw [← CStarRing.norm_star_mul_self, hf.isSelfAdjoint.star_eq, hf.isIdempotentElem.eq]
  have hfn' : ‖f‖ ≤ 1 := by nlinarith [norm_nonneg f]
  have hvn : ‖v‖ * ‖v‖ = ‖f‖ := by rw [← CStarRing.norm_star_mul_self, hv]
  nlinarith [norm_nonneg v]

/-- The final support condition and the initial projection identity imply
that the partial isometry lands in the requested corner. -/
theorem mul_eq_self_of_final_projection (e f v : P) (hf : IsStarProjection f)
    (hv : star v * v = f) (hev : e * (v * star v) = v * star v) : e * v = v := by
  have hvf := mul_initial_projection f v hf hv
  calc
    e * v = e * (v * f) := by rw [hvf]
    _ = (e * (v * star v)) * v := by rw [← hv]; noncomm_ring
    _ = (v * star v) * v := by rw [hev]
    _ = v * f := by rw [← hv]; noncomm_ring
    _ = v := hvf

/-- Conjugation by the partial isometry is an actual ambient corner element. -/
def partialIsometryCornerMap (e f : P) (he : IsStarProjection e) (hf : IsStarProjection f)
    (v : P) (hv : star v * v = f) (hev : e * (v * star v) = v * star v)
    (z : CStarCorner f hf) : CStarCorner e he :=
  ⟨v * (z : P) * star v, by
    have hel := mul_eq_self_of_final_projection e f v hf hv hev
    have her : star v * e = star v := by
      simpa only [star_mul, he.isSelfAdjoint.star_eq] using congrArg star hel
    constructor
    · rw [← mul_assoc, ← mul_assoc, hel]
    · rw [mul_assoc, her]⟩

/-- The original corner element is recovered exactly. -/
theorem partialIsometryCornerMap_recover (e f : P)
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (v : P) (hv : star v * v = f) (hev : e * (v * star v) = v * star v)
    (z : CStarCorner f hf) :
    star v * (partialIsometryCornerMap e f he hf v hv hev z : P) * v = z := by
  change star v * (v * (z : P) * star v) * v = z
  calc
    _ = (star v * v) * (z : P) * (star v * v) := by noncomm_ring
    _ = z := by rw [hv, z.property.1, z.property.2]

theorem norm_partialIsometryCornerMap_le (e f : P)
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (v : P) (hv : star v * v = f) (hev : e * (v * star v) = v * star v)
    (z : CStarCorner f hf) :
    ‖partialIsometryCornerMap e f he hf v hv hev z‖ ≤ ‖z‖ := by
  have hn := norm_le_one_of_initial_projection v f hf hv
  change ‖v * (z : P) * star v‖ ≤ ‖(z : P)‖
  calc
    _ ≤ (‖v‖ * ‖(z : P)‖) * ‖star v‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖(z : P)‖) * 1 := by rw [norm_star]; gcongr
    _ = ‖(z : P)‖ := by ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Algebraic transport, before using any projection comparison theorem. -/
theorem corner_commutator_bound_of_partial_isometry
    (L : P →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (e f : P) (he : IsStarProjection e) (hf : IsStarProjection f)
    (v : P) (hv : star v * v = f) (hev : e * (v * star v) = v * star v)
    (hTv : T * L v = L v * T) (hTvs : T * L (star v) = L (star v) * T)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ x : CStarCorner e he, ‖commutator T (L (x : P))‖ ≤ ε * ‖x‖) :
    ∀ z : CStarCorner f hf, ‖commutator T (L (z : P))‖ ≤ ε * ‖z‖ := by
  intro z
  let x := partialIsometryCornerMap e f he hf v hv hev z
  have hz : L (z : P) = L (star v) * L (x : P) * L v := by
    rw [← map_mul, ← map_mul]
    exact congrArg L (partialIsometryCornerMap_recover e f he hf v hv hev z).symm
  have hc : commutator T (L (z : P)) =
      L (star v) * commutator T (L (x : P)) * L v := by
    rw [hz]
    unfold commutator
    calc
      _ = (T * L (star v)) * L (x : P) * L v -
          L (star v) * L (x : P) * (L v * T) := by noncomm_ring
      _ = (L (star v) * T) * L (x : P) * L v -
          L (star v) * L (x : P) * (T * L v) := by rw [hTvs, ← hTv]
      _ = _ := by noncomm_ring
  have hvn : ‖L v‖ ≤ 1 :=
    (NonUnitalStarAlgHom.norm_apply_le L v).trans (norm_le_one_of_initial_projection v f hf hv)
  have hvsn : ‖L (star v)‖ ≤ 1 := by
    rw [map_star, norm_star]
    exact hvn
  rw [hc]
  calc
    _ ≤ (‖L (star v)‖ * ‖commutator T (L (x : P))‖) * ‖L v‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * (ε * ‖x‖)) * 1 := by gcongr; exact hbound x
    _ ≤ ε * ‖z‖ := by
      simpa only [one_mul, mul_one] using
        mul_le_mul_of_nonneg_left (norm_partialIsometryCornerMap_le e f he hf v hv hev z) hε

/-- Projection comparison can be performed in a separate included factor;
the resulting partial isometry is then mapped into the represented algebra. -/
theorem corner_commutator_bound_of_hom_comparison
    {A : Type*} [CStarAlgebra A] (φ : A →⋆ₐ[ℂ] P)
    (L : P →⋆ₐ[ℂ] (H →L[ℂ] H))
    (τ : A → ℝ) (comparison : FiniteFactorProjectionComparison τ)
    (e f : A) (he : IsStarProjection e) (hf : IsStarProjection f)
    (htrace : τ f ≤ τ e) (T : H →L[ℂ] H)
    (hcomm : ∀ a : A, T * L (φ a) = L (φ a) * T)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ z : CStarCorner (φ e) (he.map φ),
      ‖commutator T (L (z : P))‖ ≤ ε * ‖z‖) :
    ∀ z : CStarCorner (φ f) (hf.map φ),
      ‖commutator T (L (z : P))‖ ≤ ε * ‖z‖ := by
  obtain ⟨v, hv, hev⟩ := comparison e f he hf htrace
  have hvP : star (φ v) * φ v = φ f := by rw [← map_star, ← map_mul, hv]
  have hevP : φ e * (φ v * star (φ v)) = φ v * star (φ v) := by
    simpa only [map_mul, map_star] using congrArg φ hev
  exact corner_commutator_bound_of_partial_isometry L T (φ e) (φ f) (he.map φ)
    (hf.map φ) (φ v) hvP hevP (hcomm v) (by simpa only [map_star] using hcomm (star v))
    hε hbound

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (Q : StarSubalgebra ℂ P) [IsClosed (Q : Set P)]

/-- Finite-factor comparison is used in `Q` itself, ensuring that the
implementing partial isometry belongs to the algebra commuting with `T`. -/
theorem small_corner_commutator_bound_of_comparison
    (τ : Q → ℝ) (comparison : FiniteFactorProjectionComparison τ)
    (e f : Q) (he : IsStarProjection (e : P)) (hf : IsStarProjection (f : P))
    (htrace : τ f ≤ τ e) (T : H →L[ℂ] H)
    (hTQ : ∀ a : Q, T.comp (G.left (a : P)) = (G.left (a : P)).comp T)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ x : CStarCorner (e : P) he,
      ‖commutator T (G.left (x : P))‖ ≤ ε * ‖x‖) :
    ∀ z : CStarCorner (f : P) hf,
      ‖commutator T (G.left (z : P))‖ ≤ ε * ‖z‖ := by
  have heQ : IsStarProjection e :=
    ⟨Subtype.ext he.isIdempotentElem.eq, Subtype.ext he.isSelfAdjoint.star_eq⟩
  have hfQ : IsStarProjection f :=
    ⟨Subtype.ext hf.isIdempotentElem.eq, Subtype.ext hf.isSelfAdjoint.star_eq⟩
  obtain ⟨v, hv, hev⟩ := comparison e f heQ hfQ htrace
  have hvP : star (v : P) * (v : P) = (f : P) := congrArg (fun x : Q => (x : P)) hv
  have hevP : (e : P) * ((v : P) * star (v : P)) = (v : P) * star (v : P) :=
    congrArg (fun x : Q => (x : P)) hev
  exact corner_commutator_bound_of_partial_isometry G.left T (e : P) (f : P) he hf
    (v : P) hvP hevP (hTQ v) (hTQ (star v)) hε hbound

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
