import OAI.Analysis.KadisonKastler.MatrixVectorTrace
import OAI.Analysis.KadisonKastler.ClippedCoefficients

namespace OAI

/-! # The concrete von Neumann algebra of finite matrices

The commutant of the diagonal copy of `M'` consists exactly of the
operators all of whose matrix entries lie in `M`. This identifies it with
the usual C⋆-matrix algebra, including the represented normalized trace.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

/-- Pull a faithful tracial state back along a star-algebra equivalence. -/
def FaithfulTracialState.comapStarAlgEquiv {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (τ : FaithfulTracialState B) (e : A ≃⋆ₐ[ℂ] B) : FaithfulTracialState A where
  toLinearMap := τ.toLinearMap.comp e.toAlgEquiv.toLinearMap
  map_one := by
    change τ.toLinearMap (e 1) = 1
    rw [_root_.map_one, τ.map_one]
  positive x := by
    change 0 ≤ (τ.toLinearMap (e (star x * x))).re
    rw [_root_.map_mul e, StarHomClass.map_star e]
    exact τ.positive _
  positive_im x := by
    change (τ.toLinearMap (e (star x * x))).im = 0
    rw [_root_.map_mul e, StarHomClass.map_star e]
    exact τ.positive_im _
  faithful x hx := by
    change τ.toLinearMap (e (star x * x)) = 0 at hx
    rw [_root_.map_mul e, StarHomClass.map_star e] at hx
    have he := congrArg e.symm (τ.faithful _ hx)
    simpa only [e.symm_apply_apply, _root_.map_zero] using he
  tracial x y := by
    change τ.toLinearMap (e (x * y)) = τ.toLinearMap (e (y * x))
    rw [_root_.map_mul e, _root_.map_mul e]
    exact τ.tracial _ _

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype ι] [DecidableEq ι]

def matrixVonNeumann (M : VonNeumannAlgebra H) : VonNeumannAlgebra (Generator.FiniteHilbert ι H) where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ
    (Set.range fun a : Algebra M.commutant => Generator.diagonalOperator (ι := ι) a.val)
  centralizer_centralizer' := Set.centralizer_centralizer_centralizer _

omit [DecidableEq ι] in
theorem mem_matrixVonNeumann_iff_diagonal (M : VonNeumannAlgebra H)
    (T : Generator.FiniteHilbert ι H →L[ℂ] Generator.FiniteHilbert ι H) :
    T ∈ matrixVonNeumann M ↔ ∀ a : Algebra M.commutant,
      T * Generator.diagonalOperator a.val = Generator.diagonalOperator a.val * T := by
  change T ∈ StarSubalgebra.centralizer ℂ
    (Set.range fun a : Algebra M.commutant => Generator.diagonalOperator (ι := ι) a.val) ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h a
    exact (h _ ⟨a, rfl⟩).1.symm
  · intro h g hg
    obtain ⟨a, rfl⟩ := hg
    refine ⟨(h a).symm, ?_⟩
    rw [← Generator.diagonalOperator_star]
    exact (h (star a)).symm

theorem mem_matrixVonNeumann_iff_entries (M : VonNeumannAlgebra H)
    (T : Generator.FiniteHilbert ι H →L[ℂ] Generator.FiniteHilbert ι H) :
    T ∈ matrixVonNeumann M ↔ ∀ i j, Generator.operatorEntry T i j ∈ M := by
  rw [mem_matrixVonNeumann_iff_diagonal]
  constructor
  · intro h i j
    have he := Generator.operatorEntry_mem_centralizer M.commutant.toStarSubalgebra T h i j
    change Generator.operatorEntry T i j ∈ (M : Set (H →L[ℂ] H))
    simpa only [VonNeumannAlgebra.coe_toStarSubalgebra, VonNeumannAlgebra.coe_commutant,
      M.centralizer_centralizer] using he
  · intro h a
    exact Generator.diagonalOperator_commutes_of_entries a.val T
      (fun i j => VonNeumannAlgebra.mem_commutant_iff.mp a.property _ (h i j))

local instance matrixVNOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance matrixVNOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
local instance matrixVNAlgebraOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance matrixVNAlgebraStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

def matrixOperatorHom (M : VonNeumannAlgebra H) :
    CStarMatrix ι ι (Algebra M) →⋆ₐ[ℂ]
      (Generator.FiniteHilbert ι H →L[ℂ] Generator.FiniteHilbert ι H) :=
  hilbertMatrixHom.comp (coefficientMatrixMap M.toStarSubalgebra.subtype)

theorem matrixOperatorHom_apply (M : VonNeumannAlgebra H)
    (x : CStarMatrix ι ι (Algebra M)) :
    matrixOperatorHom M x = hilbertMatrix (x.map M.toStarSubalgebra.subtype) := rfl

theorem operatorEntry_matrixOperatorHom (M : VonNeumannAlgebra H)
    (x : CStarMatrix ι ι (Algebra M)) (i j : ι) :
    Generator.operatorEntry (matrixOperatorHom M x) i j = (x i j).val := by
  ext ξ
  simp [Generator.operatorEntry, matrixOperatorHom_apply, hilbertMatrix_apply,
    Generator.tupleSingle_apply, Pi.single_apply, apply_ite]

theorem matrixOperatorHom_mem (M : VonNeumannAlgebra H)
    (x : CStarMatrix ι ι (Algebra M)) : matrixOperatorHom M x ∈ matrixVonNeumann M := by
  rw [mem_matrixVonNeumann_iff_entries]
  intro i j
  rw [operatorEntry_matrixOperatorHom]
  exact (x i j).property

theorem matrixOperatorHom_injective (M : VonNeumannAlgebra H) :
    Function.Injective (matrixOperatorHom (ι := ι) M) := by
  intro x y h
  apply CStarMatrix.ext
  intro i j
  apply Subtype.ext
  simpa only [operatorEntry_matrixOperatorHom] using
    congrArg (fun T => Generator.operatorEntry T i j) h

theorem norm_matrixOperatorHom (M : VonNeumannAlgebra H)
    (x : CStarMatrix ι ι (Algebra M)) : ‖matrixOperatorHom M x‖ = ‖x‖ :=
  NonUnitalStarAlgHom.norm_map (matrixOperatorHom M) (matrixOperatorHom_injective M) x

def matrixFromOperator (M : VonNeumannAlgebra H)
    (T : Generator.FiniteHilbert ι H →L[ℂ] Generator.FiniteHilbert ι H)
    (hT : T ∈ matrixVonNeumann M) : CStarMatrix ι ι (Algebra M) :=
  CStarMatrix.ofMatrix fun i j =>
    ⟨Generator.operatorEntry T i j, (mem_matrixVonNeumann_iff_entries M T).mp hT i j⟩

theorem matrixOperatorHom_matrixFromOperator (M : VonNeumannAlgebra H)
    (T : Generator.FiniteHilbert ι H →L[ℂ] Generator.FiniteHilbert ι H)
    (hT : T ∈ matrixVonNeumann M) :
    matrixOperatorHom M (matrixFromOperator M T hT) = T := by
  ext ξ i
  simp only [matrixOperatorHom_apply, hilbertMatrix_apply, CStarMatrix.map_apply,
    matrixFromOperator]
  change (∑ j, T (Generator.tupleSingle j (ξ j)) i) = T ξ i
  have h := congrArg (fun ζ => T ζ i) (Generator.tuple_eq_sum_single ξ)
  simpa only [map_sum, WithLp.ofLp_sum, Finset.sum_apply] using h.symm

def matrixAlgebraHom (M : VonNeumannAlgebra H) :
    CStarMatrix ι ι (Algebra M) →⋆ₐ[ℂ] Algebra (matrixVonNeumann (ι := ι) M) where
  toFun x := ⟨matrixOperatorHom M x, matrixOperatorHom_mem M x⟩
  map_one' := Subtype.ext (map_one (matrixOperatorHom M))
  map_mul' x y := Subtype.ext (map_mul (matrixOperatorHom M) x y)
  map_zero' := Subtype.ext (map_zero (matrixOperatorHom M))
  map_add' x y := Subtype.ext (map_add (matrixOperatorHom M) x y)
  commutes' z := Subtype.ext (AlgHomClass.commutes (matrixOperatorHom M) z)
  map_star' x := Subtype.ext (map_star (matrixOperatorHom M) x)

def matrixAlgebraEquiv (M : VonNeumannAlgebra H) :
    CStarMatrix ι ι (Algebra M) ≃⋆ₐ[ℂ] Algebra (matrixVonNeumann (ι := ι) M) :=
  StarAlgEquiv.ofBijective (matrixAlgebraHom (ι := ι) M)
    ⟨fun _x _y h => matrixOperatorHom_injective M (congrArg Subtype.val h),
      fun T => ⟨matrixFromOperator M T.val T.property,
        Subtype.ext (matrixOperatorHom_matrixFromOperator M T.val T.property)⟩⟩

@[simp]
theorem matrixAlgebraEquiv_apply (M : VonNeumannAlgebra H)
    (x : CStarMatrix ι ι (Algebra M)) :
    (matrixAlgebraEquiv (ι := ι) M x).val = matrixOperatorHom M x := rfl

theorem matrixAlgebraEquiv_symm_operator (M : VonNeumannAlgebra H)
    (T : Algebra (matrixVonNeumann (ι := ι) M)) :
    matrixOperatorHom M ((matrixAlgebraEquiv (ι := ι) M).symm T) = T.val :=
  congrArg Subtype.val ((matrixAlgebraEquiv (ι := ι) M).apply_symm_apply T)

variable [Nonempty ι]

def matrixVonNeumannTrace (M : VonNeumannAlgebra H)
    (τ : FaithfulTracialState (Algebra M)) :
    FaithfulTracialState (Algebra (matrixVonNeumann (ι := ι) M)) :=
  (matrixTrace τ).comapStarAlgEquiv (matrixAlgebraEquiv (ι := ι) M).symm

theorem matrixVonNeumannTrace_finiteVector (M : VonNeumannAlgebra H)
    (τ : FaithfulTracialState (Algebra M)) (hτ : FiniteVectorTrace τ) :
    FiniteVectorTrace (matrixVonNeumannTrace (ι := ι) M τ) := by
  obtain ⟨k, ξ, η, hrep⟩ := matrixTrace_finiteVector_formula (ι := ι) τ
    M.toStarSubalgebra.subtype hτ
  refine ⟨k, ξ, η, ?_⟩
  intro T
  change (matrixTrace τ).toLinearMap ((matrixAlgebraEquiv (ι := ι) M).symm T) = _
  rw [hrep]
  have heq := matrixAlgebraEquiv_symm_operator M T
  change hilbertMatrix (((matrixAlgebraEquiv (ι := ι) M).symm T).map M.toStarSubalgebra.subtype) = T.val at heq
  rw [heq]

/-- The actual coordinate projections in the represented matrix algebra. -/
def matrixDiagonalProjection (M : VonNeumannAlgebra H) (i : ι) :
    Algebra (matrixVonNeumann (ι := ι) M) :=
  matrixAlgebraEquiv M ((coordinateMatrixUnits (B := Algebra M)).entry i i)

omit [Nonempty ι] in
theorem matrixDiagonalProjection_isStarProjection (M : VonNeumannAlgebra H) (i : ι) :
    IsStarProjection (matrixDiagonalProjection M i) :=
  (coordinateMatrixUnits_projection i).map (matrixAlgebraEquiv (ι := ι) M)

theorem matrixVonNeumannTrace_diagonal (M : VonNeumannAlgebra H)
    (τ : FaithfulTracialState (Algebra M)) (i : ι) :
    (matrixVonNeumannTrace (ι := ι) M τ).toLinearMap (matrixDiagonalProjection M i) =
      (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) := by
  change (matrixTrace τ).toLinearMap ((matrixAlgebraEquiv (ι := ι) M).symm
    ((matrixAlgebraEquiv (ι := ι) M) ((coordinateMatrixUnits (B := Algebra M)).entry i i))) = _
  rw [StarAlgEquiv.symm_apply_apply, matrixTrace_coordinate_diagonal]

omit [Nonempty ι] in
theorem finiteAverage_matrixDiagonalProjection (M : VonNeumannAlgebra H) :
    finiteAverage (matrixDiagonalProjection (ι := ι) M) =
      (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) •
        (1 : Algebra (matrixVonNeumann (ι := ι) M)) := by
  change _ • (∑ i, (matrixAlgebraEquiv (ι := ι) M)
    ((coordinateMatrixUnits (B := Algebra M)).entry i i)) = _
  rw [← map_sum, (coordinateMatrixUnits (B := Algebra M)).total, map_one]
  simp

end

end KadisonKastler

end OAI
