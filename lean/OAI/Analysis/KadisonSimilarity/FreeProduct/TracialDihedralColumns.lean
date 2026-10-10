import OAI.Analysis.KadisonSimilarity.FreeProduct.ActualArcCompression
import OAI.Analysis.KadisonSimilarity.FreeProduct.BaseSymmetry
import OAI.Analysis.KadisonSimilarity.FreeProduct.WordPropagationTransfer

namespace OAI

/-! Actual dihedral columns and reduced-word columns agree on the completed
tracial base space. Their normalizations are derived from the trace; equality
of the two realizations is needed only on bounded algebra vectors. -/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

section Algebra
variable {P : Type*} [Ring P] [StarRing P]

/-- An involution, regarded as a unit with itself as inverse. -/
def symmetryUnit (s : P) (hsquare : s * s = 1) : Pˣ := ⟨s, s, hsquare, hsquare⟩

omit [StarRing P] in
@[simp] theorem symmetryUnit_coe (s : P) (hsquare : s * s = 1) :
    (symmetryUnit s hsquare : P) = s := rfl

omit [StarRing P] in
@[simp] theorem symmetryUnit_inv (s : P) (hsquare : s * s = 1) :
    (symmetryUnit s hsquare)⁻¹ = symmetryUnit s hsquare := by ext; rfl

@[simp] theorem symmetryUnit_star (s : P) (hsquare : s * s = 1) (hstar : star s = s) :
    star (symmetryUnit s hsquare) = symmetryUnit s hsquare := by
  apply Units.ext
  exact hstar

omit [StarRing P] in
/-- The reflected rotation appearing in the Hankel entry is the second
involution itself. -/
theorem dihedral_inverse_mul_reflection (d s : Pˣ) (hs : s⁻¹ = s) :
    ((d * s)⁻¹ * d : Pˣ) = s := by
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one, hs]

/-- The reflection associated to a projection, written without scalar
coercions so that its algebraic identities apply in any star ring. -/
def projectionReflection (p : P) : P := p + p - 1

omit [StarRing P] in
theorem projectionReflection_eq_two_mul (p : P) : projectionReflection p = 2 * p - 1 := by
  rw [two_mul]
  rfl

@[simp] theorem projectionReflection_star (p : P) (hp : IsStarProjection p) :
    star (projectionReflection p) = projectionReflection p := by
  simp only [projectionReflection, star_sub, star_add, star_one, hp.isSelfAdjoint.star_eq]

@[simp] theorem projectionReflection_sq (p : P) (hp : IsStarProjection p) :
    projectionReflection p * projectionReflection p = 1 := by
  simp only [projectionReflection, sub_mul, mul_sub, add_mul, mul_add,
    one_mul, mul_one, hp.isIdempotentElem.eq]
  noncomm_ring

end Algebra

section TraceReflection
variable {P : Type*} [Ring P] [StarRing P] [Algebra ℂ P]

omit [StarRing P] in
/-- A half-trace projection gives a centered reflection. -/
theorem trace_projectionReflection (τ : P →ₗ[ℂ] ℂ) (hτ : τ 1 = 1)
    (p : P) (hp : τ p = (1 / 2 : ℂ)) : τ (projectionReflection p) = 0 := by
  rw [projectionReflection, map_sub, map_add, hp, hτ]
  norm_num

end TraceReflection



section TensorScaling
variable {J E F H : Type*}
  [NormedAddCommGroup J] [InnerProductSpace ℂ J]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Endpoint normalization commutes with every continuous word inclusion. -/
theorem include_scaled_endpoint {n : ℕ}
    (L : HilbertTensor J (EndpointTensor E F n) →L[ℂ] H)
    (v : J) (e : E) (x : Fin n → F) (c : ℂ) :
    L (hilbertTensorInsert v (endpointWord (c • e) x)) =
      c • L (hilbertTensorInsert v (endpointWord e x)) := by
  rw [endpointWord_smul_endpoint, map_smul, map_smul]

end TensorScaling

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (D : StarSubalgebra ℂ P)

/-- The normalized initial endpoint used by the dihedral word columns. -/
def projectionEndpoint (e : D) (t : ℝ) : G.baseSpace D :=
  dihedralNormalization t • G.baseVector D e

/-- A trace-`t` projection has Hilbert norm `sqrt t`. -/
theorem norm_projectionVector (e : D) (he : IsStarProjection e) {t : ℝ}
    (ht : 0 ≤ t) (hte : G.trace (e : P) = (t : ℂ)) :
    ‖G.baseVector D e‖ = Real.sqrt t := by
  have hsq : ‖G.baseVector D e‖ ^ 2 = t := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), G.baseVector_inner]
    change Complex.re ((G.trace.comp D.subtype.toLinearMap) (star e * e)) = t
    rw [he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq]
    exact congrArg Complex.re hte
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg t)).mp
  rw [Real.sq_sqrt ht]
  exact hsq

/-- The actual normalized endpoint has norm one. -/
theorem norm_projectionEndpoint (e : D) (he : IsStarProjection e) {t : ℝ}
    (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ)) :
    ‖G.projectionEndpoint D e t‖ = 1 := by
  rw [projectionEndpoint, norm_smul, G.norm_projectionVector D e he ht.le hte]
  have hn : ‖dihedralNormalization t‖ = (Real.sqrt t)⁻¹ := by
    simp only [dihedralNormalization, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg t))]
  rw [hn, inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr ht))]

section HalfReflection
variable [IsClosed (D : Set P)] (hτ : G.trace 1 = 1)
  (p : D) (hp : IsStarProjection p) (hhalf : G.trace (p : P) = (1 / 2 : ℂ))

/-- The actual centered letter associated to a half-trace projection. -/
def projectionReflectionLetter : centeredSubspace (G.baseVector D 1) :=
  G.baseSymmetryLetter D (projectionReflection p)
    (trace_projectionReflection (G.baseGeometry D).trace
      (G.baseGeometry_trace_one D hτ) p hhalf)

include hp in
/-- Its Hilbert norm is one, by the reflection and normalized-trace identities. -/
theorem norm_projectionReflectionLetter :
    ‖G.projectionReflectionLetter D hτ p hhalf‖ = 1 :=
  G.norm_baseSymmetryLetter D (projectionReflection p)
    (trace_projectionReflection (G.baseGeometry D).trace
      (G.baseGeometry_trace_one D hτ) p hhalf)
    (projectionReflection_star p hp) (projectionReflection_sq p hp) hτ

end HalfReflection

variable (A : StarSubalgebra ℂ P) [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  (hf : ScalarFree G.trace D A) (hτ : G.trace 1 = 1)
  (d : D) (s : A) (e : D)
  (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
  (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
  (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))

omit [IsClosed (A : Set P)] in
/-- The Hankel coefficient's reflected-rotation compression is the actual
restricted base symmetry. No independent compression operator is required. -/
theorem baseCompression_dihedral_reflection (dU : Pˣ) :
    G.baseCompression A (↑((dU * symmetryUnit (s : P)
      (congrArg (fun x : A => (x : P)) hssq))⁻¹ * dU) : P) =
      G.baseRepresentation A s := by
  rw [dihedral_inverse_mul_reflection _ _ (symmetryUnit_inv _ _)]
  exact G.baseCompression_subalgebra A s

/-- Actual dihedral word inclusion, with all base-space and compression data
supplied by the ambient tracial representation. -/
def tracialDihedralInclusion (k : ℕ) : G.baseSpace A →ₗᵢ[ℂ] H :=
  actualDihedralInclusion G.trace hτ G.tracial G.vector G.inner_vector D A hf
    (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))
    (symmetryUnit (s : P) (congrArg (fun x : A => (x : P)) hssq)) (e : P)
    d.property s.property e.property hd0 hs0 (symmetryUnit_inv _ _) (symmetryUnit_inv _ _)
    (symmetryUnit_star _ _ (congrArg (fun x : D => (x : P)) hdstar))
    (symmetryUnit_star _ _ (congrArg (fun x : A => (x : P)) hsstar))
    (congrArg (fun x : D => (x : P)) he.isSelfAdjoint.star_eq)
    (congrArg (fun x : D => (x : P)) he.isIdempotentElem.eq)
    (G.baseVector A) (G.baseVector_inner A) (G.baseVector_dense A) t ht hte k

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
@[simp] theorem tracialDihedralInclusion_apply (k : ℕ) (b : A) :
    G.tracialDihedralInclusion D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0 he ht hte k
      (G.baseVector A b) =
      dihedralNormalization t • G.vector ((e : P) * ((s : P) * (d : P)) ^ k * (b : P)) := by
  simp only [tracialDihedralInclusion, actualDihedralInclusion,
    dihedralWordIsometry_apply, symmetryUnit_coe]

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
/-- The dihedral columns are orthogonal on all completed base vectors. -/
theorem inner_tracialDihedralInclusion (k j : ℕ) (v w : G.baseSpace A) :
    inner ℂ
      (G.tracialDihedralInclusion D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0 he ht hte k v)
      (G.tracialDihedralInclusion D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0 he ht hte j w) =
      if k = j then inner ℂ v w else 0 := by
  unfold tracialDihedralInclusion
  exact inner_actualDihedralInclusion G.trace hτ G.tracial G.vector G.inner_vector D A hf
    _ _ (e : P) d.property s.property e.property hd0 hs0
    (symmetryUnit_inv _ _) (symmetryUnit_inv _ _)
    (symmetryUnit_star _ _ (congrArg (fun x : D => (x : P)) hdstar))
    (symmetryUnit_star _ _ (congrArg (fun x : A => (x : P)) hsstar))
    (congrArg (fun x : D => (x : P)) he.isSelfAdjoint.star_eq)
    (congrArg (fun x : D => (x : P)) he.isIdempotentElem.eq)
    (G.baseVector A) (G.baseVector_inner A) (G.baseVector_dense A) t ht hte k j v w

/-- The actual finite dihedral column family on the tracial base. -/
def tracialDihedralColumns (N : ℕ) : Fin N → G.baseSpace A →L[ℂ] H := fun i =>
  (G.tracialDihedralInclusion D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0 he ht hte i.val).toContinuousLinearMap

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
/-- Orthogonality makes the assembled finite column a contraction. -/
theorem norm_tracialDihedralColumns_le_one (N : ℕ) :
    ‖sumColumns (G.tracialDihedralColumns D A hf hτ d s e hdstar hdsq hd0
      hsstar hssq hs0 he ht hte N)‖ ≤ 1 := by
  apply norm_sumColumns_le _ zero_le_one
  · intro i
    exact (G.tracialDihedralInclusion D A hf hτ d s e hdstar hdsq hd0
      hsstar hssq hs0 he ht hte i.val).norm_toContinuousLinearMap_le
  · intro i j hij v w
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    exact (G.inner_tracialDihedralInclusion D A hf hτ d s e hdstar hdsq hd0
      hsstar hssq hs0 he ht hte i.val j.val v w).trans (ite_eq_right hne)

variable (U : OrthogonalWordLevels
  (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
    (centeredSubspace (G.baseVector D 1))) H)

/-- The repeated-word column at the actual normalized projection endpoint. -/
def repeatedDihedralInclusion (k : ℕ) : G.baseSpace A →ₗᵢ[ℂ] H :=
  repeatedWordInclusion U k (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ k)
    (G.projectionEndpoint D e t) (G.baseSymmetryLetter D d hd0)
    (G.norm_projectionEndpoint D e he ht hte)
    (G.norm_baseSymmetryLetter D d hd0 hdstar hdsq hτ)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
