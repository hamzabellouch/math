import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace OAI

/-!
# Grading a quotient by a homogeneous ideal

The manuscript uses two integer gradings on a determinant hypersurface.  This
module constructs the grading on a quotient from the grading on the original
algebra; homogeneity of the defining ideal is a proved input, not a new
assumption on a headline theorem.
-/

noncomputable section

namespace StableCoordinate.HomogeneousQuotient

open DirectSum

variable {ι k A : Type*} [DecidableEq ι] [AddMonoid ι]
  [CommRing k] [CommRing A] [Algebra k A]
  (𝒜 : ι → Submodule k A) [GradedAlgebra 𝒜] (I : Ideal A)

/-- Images of homogeneous pieces in the actual ideal quotient. -/
def piece (i : ι) : Submodule k (A ⧸ I) :=
  (𝒜 i).map (Ideal.Quotient.mkₐ k I).toLinearMap

/-- The quotient map, restricted to one homogeneous piece. -/
def pieceMap (i : ι) : 𝒜 i →ₗ[k] piece 𝒜 I i :=
  LinearMap.codRestrict _
    ((Ideal.Quotient.mkₐ k I).toLinearMap.comp (𝒜 i).subtype)
    (fun x ↦ ⟨x, x.2, rfl⟩)

omit [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜] in
@[simp]
theorem coe_pieceMap (i : ι) (x : 𝒜 i) :
    (pieceMap 𝒜 I i x : A ⧸ I) = Ideal.Quotient.mk I (x : A) := rfl

/-- Decompose upstairs, then apply the quotient map to every component. -/
def decomposeBefore : A →ₗ[k] ⨁ i, piece 𝒜 I i :=
  (DirectSum.lmap (pieceMap 𝒜 I)).comp (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap

@[simp]
theorem decomposeBefore_apply (a : A) (i : ι) :
    (decomposeBefore 𝒜 I a i : A ⧸ I) =
      Ideal.Quotient.mk I (DirectSum.decompose 𝒜 a i : A) := rfl

variable (hI : I.IsHomogeneous 𝒜)

include hI

/-- Homogeneity is exactly what permits componentwise decomposition to descend. -/
theorem ideal_le_ker_decomposeBefore :
    I.restrictScalars k ≤ LinearMap.ker (decomposeBefore 𝒜 I) := by
  intro a ha
  apply DFinsupp.ext
  intro i
  apply Subtype.ext
  change Ideal.Quotient.mk I (DirectSum.decompose 𝒜 a i : A) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI i ha)

/-- The decomposition map on the quotient. -/
def decomposeQuotient : (A ⧸ I) →ₗ[k] ⨁ i, piece 𝒜 I i where
  toFun := Quotient.lift (decomposeBefore 𝒜 I) (fun a b hab ↦ by
    apply sub_eq_zero.mp
    rw [← map_sub (decomposeBefore 𝒜 I) a b]
    exact ideal_le_ker_decomposeBefore 𝒜 I hI ((Submodule.quotientRel_def I).mp hab))
  map_add' := by
    rintro ⟨a⟩ ⟨b⟩
    exact map_add (decomposeBefore 𝒜 I) a b
  map_smul' := by
    rintro r ⟨a⟩
    exact map_smul (decomposeBefore 𝒜 I) r a

@[simp]
theorem decomposeQuotient_mk (a : A) :
    decomposeQuotient 𝒜 I hI (Ideal.Quotient.mk I a) = decomposeBefore 𝒜 I a := rfl

omit hI in
/-- Recomposition of the descended homogeneous pieces is the quotient map. -/
theorem recompose_decomposeBefore :
    (DirectSum.coeLinearMap (piece 𝒜 I)).comp (decomposeBefore 𝒜 I) =
      (Ideal.Quotient.mkₐ k I).toLinearMap := by
  apply DirectSum.decompose_lhom_ext 𝒜
  intro i
  apply LinearMap.ext
  intro x
  simp [decomposeBefore, DirectSum.decomposeLinearEquiv_apply_coe]

/-- The descended decomposition has the expected left inverse. -/
theorem recompose_decomposeQuotient :
    (DirectSum.coeLinearMap (piece 𝒜 I)).comp (decomposeQuotient 𝒜 I hI) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro a
  exact DFunLike.congr_fun (recompose_decomposeBefore 𝒜 I) a

/-- The descended decomposition has the expected right inverse. -/
theorem decomposeQuotient_recompose :
    (decomposeQuotient 𝒜 I hI).comp (DirectSum.coeLinearMap (piece 𝒜 I)) =
      LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro y
  obtain ⟨a, ha, hay⟩ := y.2
  have hy : y = pieceMap 𝒜 I i ⟨a, ha⟩ := Subtype.ext hay.symm
  subst y
  have hdecomp : DirectSum.decomposeLinearEquiv 𝒜 a =
      DirectSum.lof k ι (fun i ↦ 𝒜 i) i ⟨a, ha⟩ :=
    DirectSum.decomposeLinearEquiv_apply_coe 𝒜 i ⟨a, ha⟩
  simp [decomposeBefore, hdecomp]

/-- A quotient by a homogeneous ideal has a direct-sum decomposition. -/
@[implicit_reducible]
def decomposition : DirectSum.Decomposition (piece 𝒜 I) :=
  DirectSum.Decomposition.ofLinearMap (piece 𝒜 I) (decomposeQuotient 𝒜 I hI)
    (recompose_decomposeQuotient 𝒜 I hI) (decomposeQuotient_recompose 𝒜 I hI)

/-- Multiplication of homogeneous representatives descends with its degree. -/
instance pieceGradedMonoid : SetLike.GradedMonoid (piece 𝒜 I) where
  one_mem := by
    refine ⟨1, SetLike.GradedOne.one_mem, ?_⟩
    exact map_one (Ideal.Quotient.mkₐ k I)
  mul_mem := by
    rintro i j _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    refine ⟨a * b, SetLike.GradedMul.mul_mem ha hb, ?_⟩
    exact map_mul (Ideal.Quotient.mkₐ k I) a b

/-- The quotient algebra carries the induced grading, with no restriction on
negative degrees or on the grading monoid. -/
@[implicit_reducible]
def gradedAlgebra : GradedAlgebra (piece 𝒜 I) where
  toDecomposition := decomposition 𝒜 I hI
  toGradedMonoid := pieceGradedMonoid 𝒜 I

/-- Homogeneous projections commute with the quotient map. -/
@[simp]
theorem proj_mk (i : ι) (a : A) :
    letI : GradedAlgebra (piece 𝒜 I) := gradedAlgebra 𝒜 I hI
    GradedAlgebra.proj (piece 𝒜 I) i (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk I (GradedAlgebra.proj 𝒜 i a) := rfl

omit [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜] hI in
/-- A homogeneous representative gives a homogeneous quotient element. -/
theorem mk_mem_piece {i : ι} {a : A} (ha : a ∈ 𝒜 i) :
    Ideal.Quotient.mk I a ∈ piece 𝒜 I i := ⟨a, ha, rfl⟩

end StableCoordinate.HomogeneousQuotient

end

end OAI
