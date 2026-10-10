import OAI.Analysis.KadisonSimilarity.Tracial.TracialCornerExpectations
import OAI.Analysis.KadisonSimilarity.Tracial.TracialCornerRepresentations
import OAI.Analysis.KadisonSimilarity.FreeProduct.ActualArcCompression

namespace OAI

/-! The normalized tracial Hilbert representation of an actual C-star corner.
Its density and action are inherited from the ambient tracial representation. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (p : P) (hp : IsStarProjection p)

def cornerAlgebraVector : CStarCorner p hp →ₗ[ℂ] G.corner p p where
  toFun a := ⟨G.vector (a : P), by
    rw [G.mem_corner]
    exact ⟨by rw [G.left_vector, a.property.1], by rw [G.right_vector, a.property.2]⟩⟩
  map_add' a b := Subtype.ext (G.vector.map_add (a : P) (b : P))
  map_smul' c a := Subtype.ext (G.vector.map_smul c (a : P))

@[simp] theorem cornerAlgebraVector_coe (a : CStarCorner p hp) :
    (G.cornerAlgebraVector p hp a : H) = G.vector (a : P) := rfl

theorem cornerAlgebraVector_dense : DenseRange (G.cornerAlgebraVector p hp) := by
  apply (G.corner_vectors_dense p p hp.isIdempotentElem hp.isIdempotentElem).mono
  rintro x ⟨a, rfl⟩
  refine ⟨CStarCorner.compress p hp a, ?_⟩
  apply Subtype.ext
  exact (G.cornerProjection_vector p p a).symm

/-- Rescale the ordinary corner vectors so that their inner product is
the normalized corner trace. -/
def normalizedCornerVector (c : ℂ) : CStarCorner p hp →ₗ[ℂ] G.corner p p :=
  c • G.cornerAlgebraVector p hp

@[simp] theorem normalizedCornerVector_coe (c : ℂ) (a : CStarCorner p hp) :
    (G.normalizedCornerVector p hp c a : H) = c • G.vector (a : P) := rfl

theorem normalizedCornerVector_dense (c : ℂ) (hc : c ≠ 0) :
    DenseRange (G.normalizedCornerVector p hp c) := by
  exact (Homeomorph.smulOfNeZero c hc).surjective.denseRange.comp
    (G.cornerAlgebraVector_dense p hp) (Homeomorph.smulOfNeZero c hc).continuous

/-- The corner representation is constructed without a new GNS or
free-product existence assumption. Only the scalar normalization is chosen. -/
def cornerGeometry (c : ℂ) (hc : c ≠ 0) (hcτ : star c * c = (G.trace p)⁻¹) :
    TracialCornerGeometry (CStarCorner p hp) (G.corner p p) where
  trace := CStarCorner.normalizedTrace p hp G.trace
  vector := G.normalizedCornerVector p hp c
  left := G.cornerRepresentation p hp p
  inner_vector a b := by
    change inner ℂ (c • G.vector (a : P)) (c • G.vector (b : P)) = _
    rw [inner_smul_left, inner_smul_right, G.inner_vector]
    change star c * (c * G.trace (star (a : P) * (b : P))) =
      (G.trace p)⁻¹ * G.trace (star (a : P) * (b : P))
    rw [← mul_assoc, hcτ]
  tracial := CStarCorner.normalizedTrace_tracial p hp G.trace G.tracial
  dense_vector := G.normalizedCornerVector_dense p hp c hc
  left_vector a b := by
    apply Subtype.ext
    change G.left (a : P) (c • G.vector (b : P)) = c • G.vector ((a : P) * (b : P))
    rw [map_smul, G.left_vector]

theorem cornerGeometry_vector_injective (c : ℂ) (hc : c ≠ 0)
    (hcτ : star c * c = (G.trace p)⁻¹) (hf : Function.Injective G.vector) :
    Function.Injective (G.cornerGeometry p hp c hc hcτ).vector := by
  intro a b hab
  apply Subtype.ext
  apply hf
  have h := congrArg (fun x : G.corner p p => (x : H)) hab
  change c • G.vector (a : P) = c • G.vector (b : P) at h
  exact (smul_right_injective H hc) h

/-- The positive trace supplies the concrete inverse-square-root scalar. -/
theorem cornerNormalization_ne_zero {t : ℝ} (ht : 0 < t) :
    dihedralNormalization t ≠ 0 := by
  intro hz
  have h := dihedralNormalization_identity ht
  rw [hz, star_zero, zero_mul, zero_mul] at h
  exact zero_ne_one h

/-- The normalized tracial representation on `pL²(P)p`, with the scalar
chosen from the actual trace of `p`. -/
def normalizedCornerGeometry {t : ℝ} (ht : 0 < t) (htp : G.trace p = (t : ℂ)) :
    TracialCornerGeometry (CStarCorner p hp) (G.corner p p) :=
  G.cornerGeometry p hp (dihedralNormalization t) (cornerNormalization_ne_zero ht)
    (by rw [htp]; exact dihedralNormalization_sq ht)

theorem normalizedCornerGeometry_trace_one {t : ℝ} (ht : 0 < t)
    (htp : G.trace p = (t : ℂ)) : (G.normalizedCornerGeometry p hp ht htp).trace 1 = 1 := by
  apply CStarCorner.normalizedTrace_one
  rw [htp]
  exact_mod_cast ht.ne'

theorem normalizedCornerGeometry_vector_injective {t : ℝ} (ht : 0 < t)
    (htp : G.trace p = (t : ℂ)) (hf : Function.Injective G.vector) :
    Function.Injective (G.normalizedCornerGeometry p hp ht htp).vector :=
  G.cornerGeometry_vector_injective p hp _ _ _ hf

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
