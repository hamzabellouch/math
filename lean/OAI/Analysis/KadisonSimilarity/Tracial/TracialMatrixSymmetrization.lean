import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialEmbeddedWordStructure
import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeProductMatrixContinuity
import OAI.Analysis.KadisonSimilarity.FreeProduct.CompactHaarIntegrability
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Instances.Matrix

namespace OAI

/-! The compact groups in free-product symmetrization are the actual matrix
unitary groups. Their compatibility follows from the nested matrix embeddings
and uniqueness of the trace-preserving extension on the two factors. -/

noncomputable section
namespace KadisonSimilarity

section Conjugation

variable {H Γ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Group Γ]

omit [CompleteSpace H] in
/-- Conjugation transports a commutator through its actual covariance. -/
theorem commutator_unitaryConjugate_of_covariance
    (U : Γ →* (H →L[ℂ] H)) (T B C : H →L[ℂ] H) (g : Γ)
    (hcov : U g⁻¹ * B = C * U g⁻¹) :
    commutator (unitaryConjugate U T g) B =
      unitaryConjugate U (commutator T C) g := by
  have hi : U g * U g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hi' : U g⁻¹ * U g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hcov' : B * U g = U g * C := by
    calc
      B * U g = (U g * U g⁻¹) * B * U g := by rw [hi, one_mul]
      _ = U g * (U g⁻¹ * B) * U g := by simp only [mul_assoc]
      _ = U g * (C * U g⁻¹) * U g := by rw [hcov]
      _ = U g * C := by simp only [mul_assoc, hi', mul_one]
  change U g * T * U g⁻¹ * B - B * (U g * T * U g⁻¹) =
    U g * (T * C - C * T) * U g⁻¹
  rw [mul_sub, sub_mul]
  congr 1
  · calc
      U g * T * U g⁻¹ * B = U g * T * (U g⁻¹ * B) := mul_assoc _ _ _
      _ = U g * T * (C * U g⁻¹) := by rw [hcov]
      _ = U g * (T * C) * U g⁻¹ := by simp only [mul_assoc]
  · calc
      B * (U g * T * U g⁻¹) = (B * U g) * (T * U g⁻¹) := by simp only [mul_assoc]
      _ = (U g * C) * (T * U g⁻¹) := by rw [hcov']
      _ = U g * (C * T) * U g⁻¹ := by simp only [mul_assoc]

end Conjugation

namespace TracialCornerGeometry

open MeasureTheory TopologicalSpace
open scoped Topology CStarAlgebra ComplexOrder

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (D : Set P)]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)
  (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
  (hext : ∀ j, G.MatrixConjugationExtensionInput D (M.embedding j) A)

/-- A nested matrix star embedding maps the compact unitary groups. -/
def matrixStageUnitaryInclusion (i j : ℕ) (h : i ≤ j) :
    Matrix.unitaryGroup (I i) ℂ →* Matrix.unitaryGroup (I j) ℂ :=
  (Unitary.map (StarMonoidHom.ofClass (M.inclusion i j h))).toMonoidHom

omit [∀ j, Nonempty (I j)] in
theorem matrixStageUnitaryInclusion_embedding (i j : ℕ) (h : i ≤ j)
    (u : Matrix.unitaryGroup (I i) ℂ) :
    M.embedding j (G.matrixStageUnitaryInclusion D M i j h u : Matrix (I j) (I j) ℂ) =
      M.embedding i (u : Matrix (I i) (I i) ℂ) :=
  M.compatible i j h u

include hgen hfaithful in
omit [∀ j, Nonempty (I j)] in
/-- The ambient extension does not depend on the matrix stage used to
represent the same unitary in the factor. -/
theorem chosenMatrixExtension_compatible (i j : ℕ) (h : i ≤ j)
    (u : Matrix.unitaryGroup (I i) ℂ) :
    G.chosenMatrixExtension A D (M.embedding j) (hext j)
        (G.matrixStageUnitaryInclusion D M i j h u) =
      G.chosenMatrixExtension A D (M.embedding i) (hext i) u := by
  apply G.hom_eq_of_factor_eq A D hgen hfaithful
  · exact G.chosenMatrixExtension_trace A D _ _ _
  · exact G.chosenMatrixExtension_trace A D _ _ _
  · intro a
    rw [G.chosenMatrixExtension_base, G.chosenMatrixExtension_base]
  · intro d
    rw [G.chosenMatrixExtension_other, G.chosenMatrixExtension_other]
    congr 1
    simp only [matrixConjugateLetter, G.matrixStageUnitaryInclusion_embedding]

include hgen hfaithful in
omit [∀ j, Nonempty (I j)] in
/-- Compatibility of the actual Hilbert-space representations is proved
on dense algebra vectors. -/
theorem tracialMatrixUnitaryRepresentation_compatible (i j : ℕ) (h : i ≤ j)
    (u : Matrix.unitaryGroup (I i) ℂ) :
    G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j
        (G.matrixStageUnitaryInclusion D M i j h u) =
      G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext i u := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  refine G.dense_vector.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  simp only [tracialMatrixUnitaryRepresentation, G.matrixExtensionUnitaryRepresentation_vector]
  rw [G.chosenMatrixExtension_compatible A D M hgen hfaithful hext i j h u]

/-- Forgetting the unitary subtype gives the group homomorphism consumed
by the weak Haar integral. -/
def tracialMatrixUnitaryOperator (j : ℕ) :
    Matrix.unitaryGroup (I j) ℂ →* (H →L[ℂ] H) :=
  (unitary (H →L[ℂ] H)).subtype.comp
    (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j)

omit [∀ j, Nonempty (I j)] in
theorem tracialMatrixUnitaryOperator_star (j : ℕ) (u : Matrix.unitaryGroup (I j) ℂ) :
    (G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j u).adjoint =
      G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j u⁻¹ := by
  change (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j u :
    H →L[ℂ] H).adjoint =
      (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j u⁻¹ : H →L[ℂ] H)
  rw [← ContinuousLinearMap.star_eq_adjoint, ← Unitary.coe_star]
  have hs : star (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j u) =
      G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j u⁻¹ := by
    rw [Unitary.star_eq_inv, map_inv]
  exact congrArg (fun w : unitary (H →L[ℂ] H) => (w : H →L[ℂ] H)) hs

omit [∀ j, Nonempty (I j)] in
theorem norm_tracialMatrixUnitaryOperator_le (j : ℕ) (u : Matrix.unitaryGroup (I j) ℂ) :
    ‖G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j u‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖G.automorphismUnitary
    (G.matrixExtensionAutomorphism A D (M.embedding j) hgen hfaithful (hext j) u)
    (fun a => G.matrixExtensionAutomorphism_trace A D (M.embedding j) hgen hfaithful
      (hext j) u a) x‖ ≤ _
  rw [LinearIsometryEquiv.norm_map, one_mul]

include hgen hfaithful in
omit [∀ j, Nonempty (I j)] in
theorem tracialMatrixUnitaryOperator_compatible (i j : ℕ) (h : i ≤ j)
    (u : Matrix.unitaryGroup (I i) ℂ) :
    G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j
        (G.matrixStageUnitaryInclusion D M i j h u) =
      G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext i u := by
  exact congrArg (fun v : unitary (H →L[ℂ] H) => (v : H →L[ℂ] H))
    (G.tracialMatrixUnitaryRepresentation_compatible A D M hgen hfaithful hext i j h u)

omit [∀ j, Nonempty (I j)] in
theorem tracialMatrixUnitaryOperator_fixes_base (j : ℕ) (u : Matrix.unitaryGroup (I j) ℂ) :
    (G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j u).comp
        (G.baseInclusion A).toContinuousLinearMap = (G.baseInclusion A).toContinuousLinearMap := by
  ext x
  exact G.matrixExtensionUnitaryRepresentation_base A D (M.embedding j) hgen hfaithful
    (hext j) u x

omit [∀ j, Nonempty (I j)] in
theorem tracialMatrixUnitaryOperator_stronglyContinuous (j : ℕ) (x : H) :
    Continuous (fun u => G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j u x) :=
  G.matrixExtensionUnitaryRepresentation_stronglyContinuous A D (M.embedding j)
    hgen hfaithful (hext j) x

local instance matrixUnitaryCompactSpace (j : ℕ) : CompactSpace (Matrix.unitaryGroup (I j) ℂ) := by
  apply isCompact_iff_compactSpace.mp
  have hK : IsCompact (Set.pi Set.univ fun _ : I j =>
      Set.pi Set.univ fun _ : I j => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  apply hK.of_isClosed_subset (isClosed_unitary (R := Matrix (I j) (I j) ℂ))
  intro x hx k _ l _
  change dist (x k l) 0 ≤ 1
  rw [dist_zero_right]
  have hx' : CStarMatrix.ofMatrix x ∈ unitary (CStarMatrix (I j) (I j) ℂ) := hx
  exact (CStarMatrix.norm_entry_le_norm (M := CStarMatrix.ofMatrix x)).trans
    (le_of_eq (CStarRing.norm_coe_unitary ⟨CStarMatrix.ofMatrix x, hx'⟩))

local instance matrixUnitaryMeasurableSpace (j : ℕ) :
    MeasurableSpace (Matrix.unitaryGroup (I j) ℂ) := borel _
local instance matrixUnitaryBorelSpace (j : ℕ) : BorelSpace (Matrix.unitaryGroup (I j) ℂ) := ⟨rfl⟩

/-- The weak integrability needed for the actual Haar average is a
consequence of the proved strong continuity. -/
theorem weaklyIntegrable_tracialMatrixUnitaryConjugate (j : ℕ)
    (μ : Measure (Matrix.unitaryGroup (I j) ℂ)) [IsFiniteMeasure μ] (T : H →L[ℂ] H) :
    WeaklyIntegrable μ
      (unitaryConjugate (G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j) T) :=
  weaklyIntegrable_unitaryConjugate μ _
    (G.tracialMatrixUnitaryOperator_star A D M hgen hfaithful hext j)
    (G.tracialMatrixUnitaryOperator_stronglyContinuous A D M hgen hfaithful hext j) T

/-- The original manuscript hypothesis is uniform over all projections of
the selected trace in the other free factor. -/
def TraceCornerBound (T : H →L[ℂ] H) (t ε : ℝ) : Prop :=
  ∀ (e : P) (he : IsStarProjection e), e ∈ D → G.trace e = (t : ℂ) →
    ∀ x : CStarCorner e he, ‖commutator T (G.left (x : P))‖ ≤ ε * ‖x‖

omit [∀ j, Nonempty (I j)] in
theorem tracialMatrixUnitaryConjugate_commutator (T : H →L[ℂ] H)
    (j : ℕ) (u : Matrix.unitaryGroup (I j) ℂ) (x : P) :
    commutator (unitaryConjugate (G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j)
      T u) (G.left x) =
    unitaryConjugate (G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j)
      (commutator T (G.left (G.chosenMatrixExtension A D (M.embedding j) (hext j) u⁻¹ x)))
      u := by
  apply commutator_unitaryConjugate_of_covariance
  ext v
  exact G.matrixExtensionUnitaryRepresentation_left A D (M.embedding j) hgen hfaithful
    (hext j) u⁻¹ x v

omit [∀ j, Nonempty (I j)] in
theorem tracialMatrixUnitaryConjugate_commutes_factor (T : H →L[ℂ] H)
    (hTD : ∀ d : D, T.comp (G.left (d : P)) = (G.left (d : P)).comp T)
    (j : ℕ) (u : Matrix.unitaryGroup (I j) ℂ) (d : D) :
    commutator (unitaryConjugate (G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j)
      T u) (G.left (d : P)) = 0 := by
  rw [G.tracialMatrixUnitaryConjugate_commutator A D M hgen hfaithful hext]
  have hd : G.chosenMatrixExtension A D (M.embedding j) (hext j) u⁻¹ (d : P) ∈ D := by
    rw [G.chosenMatrixExtension_other]
    exact (matrixConjugateLetter D (M.embedding j) u⁻¹ d).property
  have hz : commutator T
      (G.left (G.chosenMatrixExtension A D (M.embedding j) (hext j) u⁻¹ (d : P))) = 0 :=
    sub_eq_zero.mpr (hTD ⟨_, hd⟩)
  rw [hz]
  simp only [unitaryConjugate, mul_zero, zero_mul]

omit [∀ j, Nonempty (I j)] in
theorem tracialMatrixUnitaryConjugate_cornerBound (T : H →L[ℂ] H) {t ε : ℝ}
    (hT : G.TraceCornerBound D T t ε) (j : ℕ) (u : Matrix.unitaryGroup (I j) ℂ) :
    G.TraceCornerBound D
      (unitaryConjugate (G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j) T u) t ε := by
  intro e he heD het x
  let Φ := G.chosenMatrixExtension A D (M.embedding j) (hext j) u⁻¹
  have he' : IsStarProjection (Φ e) := by
    constructor
    · change Φ e * Φ e = Φ e
      rw [← map_mul, he.isIdempotentElem.eq]
    · change star (Φ e) = Φ e
      rw [← map_star, he.isSelfAdjoint.star_eq]
  have heD' : Φ e ∈ D := by
    dsimp only [Φ]
    rw [G.chosenMatrixExtension_other A D (M.embedding j) (hext j) u⁻¹ ⟨e, heD⟩]
    exact (matrixConjugateLetter D (M.embedding j) u⁻¹ ⟨e, heD⟩).property
  have het' : G.trace (Φ e) = (t : ℂ) :=
    (G.chosenMatrixExtension_trace A D (M.embedding j) (hext j) u⁻¹ e).trans het
  let x' : CStarCorner (Φ e) he' := ⟨Φ (x : P), by
    constructor
    · rw [← map_mul, x.property.1]
    · rw [← map_mul, x.property.2]⟩
  have hn : ‖x'‖ = ‖x‖ :=
    StarAlgEquiv.norm_map
      (G.matrixExtensionAutomorphism A D (M.embedding j) hgen hfaithful (hext j) u⁻¹) (x : P)
  rw [G.tracialMatrixUnitaryConjugate_commutator A D M hgen hfaithful hext]
  apply (norm_unitaryConjugate_le _
    (G.norm_tracialMatrixUnitaryOperator_le A D M hgen hfaithful hext j) _ u).trans
  simpa only [hn] using hT (Φ e) he' heD' het' x'

/-- Actual normalized Haar measure of the finite matrix unitary group. -/
def tracialMatrixHaarProbability (j : ℕ) : Measure (Matrix.unitaryGroup (I j) ℂ) :=
  Measure.haarMeasure ⊤

instance tracialMatrixHaarProbability_probability (j : ℕ) :
    IsProbabilityMeasure (tracialMatrixHaarProbability (I := I) j) := by
  apply IsProbabilityMeasure.mk
  exact Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts (Matrix.unitaryGroup (I j) ℂ)))

instance tracialMatrixHaarProbability_leftInvariant (j : ℕ) :
    (tracialMatrixHaarProbability (I := I) j).IsMulLeftInvariant :=
  inferInstanceAs (Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup (I j) ℂ))).IsMulLeftInvariant

/-- The test elements supported by a projection of the selected trace. -/
def traceCornerElements (t : ℝ) : Set P :=
  {x | ∃ (e : P) (_ : IsStarProjection e), e ∈ D ∧ G.trace e = (t : ℂ) ∧
    e * x = x ∧ x * e = x}

include hgen hfaithful in
/-- Simultaneous compact averaging produces the exact additional symmetries
used by word classification. It preserves the original base compression and
the uniform corner bound. No invariant limiting operator is an input. -/
theorem exists_tracially_symmetrized (T : H →L[ℂ] H)
    (hTD : ∀ d : D, T.comp (G.left (d : P)) = (G.left (d : P)).comp T)
    {t ε : ℝ} (hε : 0 ≤ ε) (hcorner : G.TraceCornerBound D T t ε) :
    ∃ Y : H →L[ℂ] H,
      ‖Y‖ ≤ ‖T‖ ∧
      (∀ d : D, Y.comp (G.left (d : P)) = (G.left (d : P)).comp Y) ∧
      (∀ j w, Y.comp
          (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H) =
        (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H).comp Y) ∧
      G.TraceCornerBound D Y t ε ∧ G.baseOperator A Y = G.baseOperator A T := by
  let U := G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext
  let Test := D ⊕ G.traceCornerElements D t
  let test : Test → H →L[ℂ] H := Sum.elim (fun d => G.left (d : P)) (fun x => G.left (x : P))
  let bound : Test → ℝ := Sum.elim (fun _ => 0) (fun x => ε * ‖(x : P)‖)
  have hbound : ∀ x, 0 ≤ bound x := by
    intro x
    cases x with
    | inl d => exact le_refl 0
    | inr x => exact mul_nonneg hε (norm_nonneg _)
  have htest : ∀ j w x, ‖commutator (unitaryConjugate (U j) T w) (test x)‖ ≤ bound x := by
    intro j w x
    cases x with
    | inl d =>
      change ‖commutator (unitaryConjugate (U j) T w) (G.left (d : P))‖ ≤ 0
      rw [G.tracialMatrixUnitaryConjugate_commutes_factor A D M hgen hfaithful hext T hTD]
      simp only [norm_zero, le_refl]
    | inr x =>
      obtain ⟨e, he, heD, het, hxleft, hxright⟩ := x.property
      exact G.tracialMatrixUnitaryConjugate_cornerBound A D M hgen hfaithful hext T hcorner
        j w e he heD het ⟨x, hxleft, hxright⟩
  obtain ⟨Y, hYnorm, hYW, hYtest, hbase⟩ := exists_simultaneously_symmetrized
    (tracialMatrixHaarProbability (I := I)) U
    (G.norm_tracialMatrixUnitaryOperator_le A D M hgen hfaithful hext)
    (G.tracialMatrixUnitaryOperator_star A D M hgen hfaithful hext)
    (fun i j h u => G.matrixStageUnitaryInclusion D M i j h u)
    (G.tracialMatrixUnitaryOperator_compatible A D M hgen hfaithful hext) T
    (fun j => G.weaklyIntegrable_tracialMatrixUnitaryConjugate A D M hgen hfaithful hext j _ T)
    (G.baseInclusion A).toContinuousLinearMap
    (G.tracialMatrixUnitaryOperator_fixes_base A D M hgen hfaithful hext)
    test bound hbound htest
  refine ⟨Y, hYnorm, ?_, ?_, ?_, ?_⟩
  · intro d
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    exact le_antisymm (hYtest (.inl d)) (norm_nonneg _)
  · intro j w
    exact sub_eq_zero.mp (hYW j w)
  · intro e he heD het x
    exact hYtest (.inr ⟨(x : P), e, he, heD, het, x.property.1, x.property.2⟩)
  · exact hbase

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
