import OAI.Analysis.Pureness.Comparison.SpatialCompactTensor
import OAI.Analysis.Pureness.Comparison.MatrixUnitCorners
import OAI.Analysis.Pureness.Comparison.FaithfulGNS

namespace OAI
noncomputable section
open scoped CStarAlgebra Topology
namespace CuntzComparison
open CuntzTrace
variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))

instance spatialCompactAlgebra_closed : IsClosed (spatialCompactAlgebra π : Set (StabilizationOperators H)) :=
  NonUnitalStarSubalgebra.isClosed_topologicalClosure _

abbrev SpatialStabilization := spatialCompactAlgebra π

instance : NonUnitalCStarAlgebra (SpatialStabilization π) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (spatialCompactAlgebra π)

def spatialRepresentationInto : MatrixLimit A →⋆ₙₐ[ℂ] SpatialStabilization π where
  toFun x := ⟨spatialRepresentation π x, by
    change spatialRepresentation π x ∈ spatialCompactAlgebra π
    rw [spatialCompactAlgebra_eq_matrixAlgebra]
    exact spatialRepresentation_mem π x⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)
  map_mul' x y := Subtype.ext (map_mul _ x y)
  map_smul' c x := Subtype.ext (map_smul _ c x)
  map_star' x := Subtype.ext (map_star _ x)

def spatialEquiv (hπ : Function.Injective π) : MatrixLimit A ≃⋆ₐ[ℂ] SpatialStabilization π :=
  StarAlgEquiv.ofBijective (spatialRepresentationInto π) ⟨
    fun x y h => (spatialRepresentation_isometry π hπ).injective (congrArg Subtype.val h),
    fun T => by
      have ht : T.1 ∈ Set.range (spatialRepresentation π) := by
        rw [spatialRepresentation_range_compact π hπ]
        exact T.2
      obtain ⟨x,hx⟩ := ht
      exact ⟨x,Subtype.ext hx⟩⟩

@[simp] theorem spatialEquiv_norm (hπ : Function.Injective π) (x : MatrixLimit A) :
    ‖spatialEquiv π hπ x‖ = ‖x‖ := spatialRepresentation_norm π hπ x

def spatialStage (n : ℕ) : FinMatrix A n →⋆ₙₐ[ℂ] SpatialStabilization π :=
  (spatialRepresentationInto π).comp (matrixLimitStage n)

lemma spatialStage_eq_equiv (hπ : Function.Injective π) (n : ℕ) (M : FinMatrix A n) :
    spatialStage π n M = spatialEquiv π hπ (matrixLimitStage n M) := rfl

@[simp] theorem spatialStage_coe (n : ℕ) (M : FinMatrix A n) :
    (spatialStage π n M : StabilizationOperators H) = spatialFinite π n M :=
  spatialRepresentation_stage π n M

theorem spatialStage_isometry (hπ : Function.Injective π) (n : ℕ) : Isometry (spatialStage π n) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro M
  change ‖spatialRepresentation π (matrixLimitStage n M)‖ = ‖M‖
  rw [spatialRepresentation_norm π hπ, matrixLimitStage_norm]

private theorem transport_full_corner {D E F : Type*}
    [NonUnitalCStarAlgebra D] [NonUnitalCStarAlgebra E] [CStarAlgebra F]
    (f : D →⋆ₙₐ[ℂ] E) (hf : Function.Bijective f) (ι : F →⋆ₙₐ[ℂ] D)
    (hc : ∀ x : D, ι 1 * x * ι 1 = x → ∃ a : F, ι a = x)
    (x : E) (hx : (f.comp ι) 1 * x * (f.comp ι) 1 = x) :
    ∃ a : F, (f.comp ι) a = x := by
  obtain ⟨y,rfl⟩ := hf.2 x
  have he (a : F) : (f.comp ι) a = f (ι a) := rfl
  rw [he] at hx
  have hy : ι 1 * y * ι 1 = y := hf.1 (by simpa only [map_mul] using hx)
  obtain ⟨a,ha⟩ := hc y hy
  exact ⟨a,congrArg f ha⟩

theorem spatialStage_full_corner (hπ : Function.Injective π) (n : ℕ) (x : SpatialStabilization π)
    (hx : spatialStage π n 1 * x * spatialStage π n 1 = x) :
    ∃ M : FinMatrix A n, spatialStage π n M = x := by
  have hb : Function.Bijective (spatialRepresentationInto π) := by
    change Function.Bijective (spatialEquiv π hπ)
    exact (spatialEquiv π hπ).bijective
  exact transport_full_corner (spatialRepresentationInto π) hb (matrixLimitStage n)
    (matrixLimitStage_full_corner n) x hx

theorem cuntzSubequiv_reflect_spatial (hπ : Function.Injective π) {n : ℕ} {a b : FinMatrix A n}
    (h : CuntzSubequiv (spatialStage π n a) (spatialStage π n b)) : CuntzSubequiv a b :=
  CuntzSubequiv.reflect_corner (spatialStage π n) (spatialStage_isometry π hπ n).injective
    (spatialStage_full_corner π hπ n) h

def TracialState.spatialEquiv [IsSimpleCStarAlgebra A] (τ : TracialState A) :
    MatrixLimit A ≃⋆ₐ[ℂ] SpatialStabilization τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom :=
  CuntzComparison.spatialEquiv τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom τ.gns_injective
end CuntzComparison

end

end OAI
