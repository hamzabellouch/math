import OAI.Analysis.KadisonSimilarity.FreeProduct.HaarCornerLetters
import OAI.Analysis.KadisonSimilarity.Tracial.TracialHalfProjectionData

namespace OAI

/-! Corner unitaries and completed half projections are transported along
the actual trace-preserving factor embedding. This retains their concrete
support projections inside the conjugated free copy. -/

noncomputable section
namespace KadisonSimilarity

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  (φ : A →⋆ₐ[ℂ] B)

/-- A unital star homomorphism restricts to a unital homomorphism between
the actual corners of corresponding projections. -/
def cornerStarAlgHom (e : A) (he : IsStarProjection e) :
    CStarCorner e he →⋆ₐ[ℂ] CStarCorner (φ e) (he.map φ) where
  toFun x := ⟨φ (x : A), by
    constructor
    · rw [← map_mul, x.property.1]
    · rw [← map_mul, x.property.2]⟩
  map_zero' := Subtype.ext (map_zero φ)
  map_one' := Subtype.ext (by simp only [CStarCorner.coe_one])
  map_add' x y := Subtype.ext (map_add φ (x : A) (y : A))
  map_mul' x y := Subtype.ext (map_mul φ (x : A) (y : A))
  commutes' c := Subtype.ext (by
    change φ ((algebraMap ℂ (CStarCorner e he) c : CStarCorner e he) : A) =
      ((algebraMap ℂ (CStarCorner (φ e) (he.map φ)) c :
        CStarCorner (φ e) (he.map φ)) : B)
    simp only [Algebra.algebraMap_eq_smul_one]
    change φ (c • ((1 : CStarCorner e he) : A)) =
      c • ((1 : CStarCorner (φ e) (he.map φ)) : B)
    rw [CStarCorner.coe_one, CStarCorner.coe_one, map_smul])
  map_star' x := Subtype.ext (map_star φ (x : A))

@[simp] theorem cornerStarAlgHom_coe (e : A) (he : IsStarProjection e)
    (x : CStarCorner e he) : (cornerStarAlgHom φ e he x : B) = φ (x : A) := rfl

def transportedCornerUnitary {e : A} {he : IsStarProjection e}
    (z : unitary (CStarCorner e he)) : unitary (CStarCorner (φ e) (he.map φ)) :=
  Unitary.map (StarMonoidHom.ofClass (cornerStarAlgHom φ e he)) z

theorem haarCornerPower_transport {e : A} {he : IsStarProjection e}
    (z : unitary (CStarCorner e he)) (k : ℤ) :
    haarCornerPower (transportedCornerUnitary φ z) k = φ (haarCornerPower z k) := by
  change ((((Unitary.map (StarMonoidHom.ofClass (cornerStarAlgHom φ e he)) z) ^ k :
    unitary (CStarCorner (φ e) (he.map φ))) : CStarCorner (φ e) (he.map φ)) : B) = _
  rw [← map_zpow]
  rfl

theorem HaarCornerMoments.transport
    (τA : A →ₗ[ℂ] ℂ) (τB : B →ₗ[ℂ] ℂ) (hφ : ∀ x, τB (φ x) = τA x)
    {e : A} {he : IsStarProjection e} (z : unitary (CStarCorner e he)) {t : ℝ}
    (hz : HaarCornerMoments τA z t) :
    HaarCornerMoments τB (transportedCornerUnitary φ z) t := by
  intro k hk
  rw [haarCornerPower_transport, hφ]
  exact hz k hk

/-- Half-trace completion and both support identities survive the factor
embedding, as does the subsequently constructed centered reflection. -/
def HalfTraceProjectionData.transport
    {τA : A →ₗ[ℂ] ℂ} {τB : B →ₗ[ℂ] ℂ} (hφ : ∀ x, τB (φ x) = τA x)
    {e : A} (Q : HalfTraceProjectionData τA e) : HalfTraceProjectionData τB (φ e) where
  projection := φ Q.projection
  isProjection := Q.isProjection.map φ
  trace_half := (hφ _).trans Q.trace_half
  left_support := by rw [← map_mul, Q.left_support]
  right_support := by rw [← map_mul, Q.right_support]

end KadisonSimilarity

end

end OAI
