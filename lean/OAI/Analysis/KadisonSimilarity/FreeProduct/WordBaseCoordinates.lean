import OAI.Analysis.KadisonSimilarity.FreeProduct.WordMultiplicities
import OAI.Analysis.KadisonSimilarity.FreeProduct.OrthogonalWordLevels
import OAI.Analysis.KadisonSimilarity.Tracial.TracialBaseSpace

namespace OAI

/-! Identify the degree-zero multiplicity operator with the actual compression
to the base algebra's tracial Hilbert space. -/

noncomputable section
namespace KadisonSimilarity

universe u
variable {E F : Type u} {B H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The first endpoint with no centered tail letters. -/
def emptyEndpoint (Ω : E) : EndpointTensor E F 0 :=
  endpointWord Ω (Fin.elim0 : Fin 0 → F)

@[simp] theorem norm_emptyEndpoint (Ω : E) : ‖emptyEndpoint (F := F) Ω‖ = ‖Ω‖ := by
  change ‖endpointInsert Ω (completedTensorWord (Fin.elim0 : Fin 0 → F))‖ = ‖Ω‖
  simp only [norm_endpointInsert, norm_completedTensorWord, Fin.prod_univ_zero, mul_one]

variable (ΩA : B)
  (U : OrthogonalWordLevels (MultiplicityWordSpace (WordMultiplicity ΩA) E F) H)
  (ΩD : E) (hΩD : ‖ΩD‖ = 1)

/-- The base Hilbert space embeds as the scalar first endpoint in degree zero. -/
def baseWordInclusion : B →ₗᵢ[ℂ] H where
  toLinearMap := (U.inclusion 0).toLinearMap.comp
    ((hilbertTensorRightInsert (emptyEndpoint (F := F) ΩD)).toLinearMap.comp
      (zeroMultiplicityEquiv ΩA).toLinearMap)
  norm_map' b := by
    change ‖U.inclusion 0 (hilbertTensorInsert (zeroMultiplicityEquiv ΩA b)
      (emptyEndpoint (F := F) ΩD))‖ = ‖b‖
    rw [LinearIsometry.norm_map, norm_hilbertTensorInsert,
      LinearIsometryEquiv.norm_map, norm_emptyEndpoint, hΩD, mul_one]

omit [CompleteSpace H] in
@[simp] theorem baseWordInclusion_apply (b : B) :
    baseWordInclusion ΩA U ΩD hΩD b =
      U.inclusion 0 (hilbertTensorInsert (zeroMultiplicityEquiv ΩA b)
        (emptyEndpoint (F := F) ΩD)) := rfl

omit [CompleteSpace H] in
/-- The degree-zero repeated-word identity determines the base operator. -/
theorem baseWordInclusion_intertwines (Y : H →L[ℂ] H)
    (T : WordMultiplicity ΩA 0 →L[ℂ] WordMultiplicity ΩA 0)
    (hY : ∀ v, Y (U.inclusion 0 (hilbertTensorInsert v (emptyEndpoint (F := F) ΩD))) =
      U.inclusion 0 (hilbertTensorInsert (T v) (emptyEndpoint (F := F) ΩD))) :
    Y.comp (baseWordInclusion ΩA U ΩD hΩD).toContinuousLinearMap =
      (baseWordInclusion ΩA U ΩD hΩD).toContinuousLinearMap.comp
        (zeroMultiplicityOperator ΩA T) := by
  ext b
  change Y (U.inclusion 0 (hilbertTensorInsert (zeroMultiplicityEquiv ΩA b)
      (emptyEndpoint (F := F) ΩD))) =
    U.inclusion 0 (hilbertTensorInsert
      (zeroMultiplicityEquiv ΩA (zeroMultiplicityOperator ΩA T b))
      (emptyEndpoint (F := F) ΩD))
  rw [hY, zeroMultiplicityOperator_intertwines]

/-- Compressing to the base-word inclusion recovers precisely the transported
canonical degree-zero operator. -/
theorem baseWordInclusion_compression (Y : H →L[ℂ] H)
    (T : WordMultiplicity ΩA 0 →L[ℂ] WordMultiplicity ΩA 0)
    (hY : ∀ v, Y (U.inclusion 0 (hilbertTensorInsert v (emptyEndpoint (F := F) ΩD))) =
      U.inclusion 0 (hilbertTensorInsert (T v) (emptyEndpoint (F := F) ΩD))) :
    (baseWordInclusion ΩA U ΩD hΩD).toContinuousLinearMap.adjoint.comp
      (Y.comp (baseWordInclusion ΩA U ΩD hΩD).toContinuousLinearMap) =
        zeroMultiplicityOperator ΩA T := by
  rw [baseWordInclusion_intertwines ΩA U ΩD hΩD Y T hY,
    ← ContinuousLinearMap.comp_assoc, LinearIsometry.adjoint_comp_self,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

section TracialBase
variable {P : Type*} [CStarAlgebra P]
  (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)
  (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) E F) H)

/-- Equality on algebra vectors identifies the abstract degree-zero inclusion
with the actual closed base subspace. The extension follows from density. -/
theorem baseWordInclusion_eq_baseInclusion
    (hword : ∀ a : A,
      baseWordInclusion (G.baseVector A 1) U ΩD hΩD (G.baseVector A a) = G.vector (a : P)) :
    baseWordInclusion (G.baseVector A 1) U ΩD hΩD = G.baseInclusion A := by
  ext b
  exact (G.baseVector_dense A).induction_on b
    (isClosed_eq (by fun_prop) (by fun_prop)) hword

/-- The degree-zero operator is the actual tracial compression, rather than
an unrelated multiplicity coefficient. -/
theorem baseOperator_eq_zeroMultiplicityOperator (Y : H →L[ℂ] H)
    (T : WordMultiplicity (G.baseVector A 1) 0 →L[ℂ] WordMultiplicity (G.baseVector A 1) 0)
    (hword : ∀ a : A,
      baseWordInclusion (G.baseVector A 1) U ΩD hΩD (G.baseVector A a) = G.vector (a : P))
    (hY : ∀ v, Y (U.inclusion 0 (hilbertTensorInsert v (emptyEndpoint (F := F) ΩD))) =
      U.inclusion 0 (hilbertTensorInsert (T v) (emptyEndpoint (F := F) ΩD))) :
    G.baseOperator A Y = zeroMultiplicityOperator (G.baseVector A 1) T := by
  have h := baseWordInclusion_compression (G.baseVector A 1) U ΩD hΩD Y T hY
  rw [baseWordInclusion_eq_baseInclusion ΩD hΩD G A U hword] at h
  exact h

end TracialBase
end KadisonSimilarity

end

end OAI
