import OAI.Analysis.KadisonSimilarity.Representation.ProperlyInfiniteStructure
import OAI.Analysis.KadisonSimilarity.Tracial.FiniteFactorTrace
import OAI.Analysis.KadisonSimilarity.Representation.FactorAssembly
import OAI.Analysis.BoundedHochschild.FiniteTypeIPieces
import OAI.Analysis.FactorGeneration.MatrixUnits

namespace OAI

/-! A finite factor with a nonzero abelian projection is a full matrix algebra.
The homogeneous central piece is the unit because the center is scalar. -/

noncomputable section
namespace KadisonSimilarity

open BoundedHochschild.KadisonRingrose HochschildCorners HochschildMatrixSystems
open scoped ComplexOrder

private def unitCornerEquiv {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (hp : IsStarProjection (1 : A)) : Corner 1 hp ≃⋆ₐ[ℂ] A where
  toFun a := a.val
  invFun a := ⟨a, by change 1 * a = a ∧ a * 1 = a; simp⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

private def matrixUnitsOfSystem {A : Type*} [CStarAlgebra A] {n : ℕ}
    (E : MatrixSystem A n) : Generator.MatrixUnitSystem (Fin n) A where
  entry := E.entry
  star_entry := E.star_entry
  mul_entry := E.entry_mul
  total := E.sum_diagonal

private theorem matrixSystem_surjective_of_abelian_diagonal
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (hfactor : ∀ a : A, (∀ b, a * b = b * a) → ∃ c : ℂ, a = algebraMap ℂ A c)
    {n : ℕ} (E : MatrixSystem A n) (i : Fin n)
    (hi : FinitePathMain.AbelianProjection (E.entry i i)) :
    Function.Surjective (matrixUnitsOfSystem E).hom := by
  intro x
  have hcomm := E.commutant_commutative_of_abelian_diagonal i hi
  have hcoeff (j k : Fin n) : ∃ c : ℂ, E.coefficient j k x = c • (1 : A) := by
    obtain ⟨c, hc⟩ := hfactor (E.coefficient j k x)
      (E.commutant_central hcomm ⟨_, E.coefficient_mem j k x⟩)
    exact ⟨c, by simpa only [Algebra.algebraMap_eq_smul_one] using hc⟩
  choose c hc using hcoeff
  refine ⟨Matrix.of c, ?_⟩
  change (∑ j, ∑ k, c j k • E.entry j k) = x
  rw [← E.reconstruct x]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [hc, mul_smul_comm, mul_one]

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : VonNeumannAlgebra H)

local instance finiteTypeIStructureClosed : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (P : Set (H →L[ℂ] H))
  infer_instance

theorem finiteMatrixFactorModel_of_homogeneous_unit
    (hfactor : ∀ a : P.toStarSubalgebra, (∀ b, a * b = b * a) →
      ∃ c : ℂ, a = algebraMap ℂ P.toStarSubalgebra c)
    (hhom : HomogeneousTypeICorner (1 : P.toStarSubalgebra)) :
    Nonempty (FiniteMatrixFactorModel P) := by
  obtain ⟨hp, n, E, i, hi⟩ := hhom
  let e := unitCornerEquiv hp
  let E' : MatrixSystem P.toStarSubalgebra n := E.mapEquiv e
  have hi' : FinitePathMain.AbelianProjection (E'.entry i i) := abelian_map_equiv e hi
  let f := (matrixUnitsOfSystem E').hom
  have hsurj : Function.Surjective f :=
    matrixSystem_surjective_of_abelian_diagonal hfactor E' i hi'
  refine ⟨{
    size := n
    size_ne_zero := Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)
    inclusion := P.toStarSubalgebra.subtype.comp f
    mem := fun a => (f a).property
    surjective := ?_ }⟩
  intro T hT
  obtain ⟨a, ha⟩ := hsurj ⟨T, hT⟩
  exact ⟨a, congrArg Subtype.val ha⟩

/-- A finite factor containing a nonzero abelian projection has the exact
finite matrix model used in the type-I commutator estimate. -/
theorem finiteMatrixFactorModel_of_abelian_projection [Nontrivial H]
    (hfinite : FiniteAlgebra P.toStarSubalgebra)
    (hfactor : ∀ a : P.toStarSubalgebra, (∀ b, a * b = b * a) →
      ∃ c : ℂ, a = algebraMap ℂ P.toStarSubalgebra c)
    (p : P.toStarSubalgebra) (hp : FinitePathMain.AbelianProjection p) (hp0 : p ≠ 0) :
    Nonempty (FiniteMatrixFactorModel P) := by
  obtain ⟨τ, _, _, htr, hf, _⟩ := exists_faithful_normal_trace P hfinite hfactor
  obtain ⟨z, hz, hz0, hhom⟩ := exists_homogeneous_piece_of_abelian_trace
    (concretePredualEquiv P) τ htr hf hp hp0
  have hz1 : z = 1 := (central_projection_zero_or_one hfactor z hz.1
    (fun a => (hz.2 a).eq)).resolve_left hz0
  exact finiteMatrixFactorModel_of_homogeneous_unit P hfactor (hz1 ▸ hhom)

end KadisonSimilarity

end

end OAI
