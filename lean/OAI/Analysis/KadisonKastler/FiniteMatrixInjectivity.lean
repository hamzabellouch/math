import OAI.Analysis.KadisonKastler.TypeIInjectivity
import OAI.Analysis.FactorGeneration.MatrixAlgebras

namespace OAI

/-! # Injectivity of a concrete full matrix algebra

The diagonal matrix units are minimal projections. Thus the concrete type-I
injectivity theorem applies to each finite matrix stage.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] {M : VonNeumannAlgebra H}
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Full matrix units give precisely the scalar center. -/
theorem scalarCenter_of_matrixUnits_surjective
    (E : MatrixUnitSystem ι (Algebra M)) (hE : Function.Surjective E.hom) :
    ScalarCenter M := by
  intro T hT hcomm
  obtain ⟨a,ha⟩ := hE ⟨T,hT⟩
  have hc : a ∈ Set.center (Matrix ι ι ℂ) := by
    rw [Semigroup.mem_center_iff]
    intro b
    apply E.injective
    rw [map_mul, map_mul, ha]
    exact Subtype.ext (hcomm (E.hom b).val (E.hom b).property)
  rw [Matrix.center_eq_range] at hc
  obtain ⟨z,hz⟩ := hc
  refine ⟨z, ?_⟩
  have hs : Matrix.scalar ι z = z • (1 : Matrix ι ι ℂ) := by
    ext i j
    simp [Matrix.scalar, Matrix.diagonal, Matrix.one_apply]
  have hm := congrArg E.hom hz
  rw [hs, map_smul, map_one, ha] at hm
  exact (congrArg Subtype.val hm).symm

omit [Nontrivial H] [Nonempty ι] in
/-- A specified diagonal matrix unit, as an algebra projection. -/
def matrixUnitDiagonalProjection (E : MatrixUnitSystem ι (Algebra M)) (o : ι) :
    AlgebraProjection M :=
  ⟨E.entry o o, ⟨by simp only [IsIdempotentElem, E.mul_entry, ite_true], E.star_entry o o⟩⟩

omit [Nonempty ι] in
/-- Each specified diagonal unit is minimal in the full matrix image. -/
theorem matrixUnitDiagonalProjection_minimal
    (E : MatrixUnitSystem ι (Algebra M)) (hE : Function.Surjective E.hom) (o : ι) :
    IsMinimalProjectionIn M (matrixUnitDiagonalProjection E o) := by
  let p := matrixUnitDiagonalProjection E o
  refine ⟨E.diagonal_ne_zero o, ?_⟩
  intro q hq
  obtain ⟨a,ha⟩ := hE q.val
  have hleft : p.val * q.val = q.val := hq
  have hqp : q.val * p.val = q.val := projection_mul_of_le hq
  have hz : q.val = a o o • p.val := by
    have h := E.sandwich a o o o
    change p.val * E.hom a * p.val = a o o • p.val at h
    rwa [ha, hleft, hqp] at h
  have hi : (a o o * a o o) • p.val = a o o • p.val := by
    calc
      _ = (a o o • p.val) * (a o o • p.val) := by
        rw [smul_mul_smul, p.property.isIdempotentElem.eq]
      _ = _ := by rw [← hz, q.property.isIdempotentElem.eq]
  have hzid : a o o * a o o = a o o := (smul_left_injective ℂ (E.diagonal_ne_zero o)) hi
  have hcases : a o o = 0 ∨ a o o = 1 := by
    have hzero : a o o * (a o o - 1) = 0 := by rw [mul_sub, mul_one, hzid, sub_self]
    rcases mul_eq_zero.mp hzero with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  rcases hcases with h | h
  · left
    simpa only [h, zero_smul] using hz
  · right
    apply Subtype.ext
    simpa only [h, one_smul] using hz

omit [Nonempty ι] in
/-- Every full matrix algebra contains a minimal projection. -/
theorem minimalProjection_of_matrixUnits_surjective
    (E : MatrixUnitSystem ι (Algebra M)) (hE : Function.Surjective E.hom) (o : ι) :
    ∃ p : AlgebraProjection M, IsMinimalProjectionIn M p :=
  ⟨matrixUnitDiagonalProjection E o, matrixUnitDiagonalProjection_minimal E hE o⟩

/-- A full matrix algebra is injective in its given Hilbert representation. -/
theorem isInjective_of_matrixUnits_surjective
    (E : MatrixUnitSystem ι (Algebra M)) (hE : Function.Surjective E.hom) :
    IsInjective M := by
  apply publishedTypeIInjectivity M
  exact ⟨scalarCenter_of_matrixUnits_surjective E hE,
    minimalProjection_of_matrixUnits_surjective E hE (Classical.arbitrary ι)⟩

/-- The concrete finite matrix image, with its proved weak closedness. -/
def matrixUnitConcreteAlgebra (E : MatrixUnitSystem ι (Algebra M)) :
    VonNeumannAlgebra H :=
  vonNeumannOfWOTClosed E.concreteAlgebra E.concreteAlgebra_wotClosed

omit [Nontrivial H] [Nonempty ι] in
/-- The represented matrix image stays in its original algebra. -/
theorem matrixUnitConcreteAlgebra_le (E : MatrixUnitSystem ι (Algebra M)) :
    matrixUnitConcreteAlgebra E ≤ M := by
  intro T hT
  exact E.concreteAlgebra_le hT

/-- The same matrix units regarded inside their concrete image. -/
def concreteMatrixUnits (E : MatrixUnitSystem ι (Algebra M)) :
    MatrixUnitSystem ι (Algebra (matrixUnitConcreteAlgebra E)) where
  entry i j := ⟨(E.entry i j).val,
    (E.mem_concreteAlgebra (E.entry i j)).mpr (E.entry_mem i j)⟩
  star_entry i j := by
    apply Subtype.ext
    change star ((E.entry i j).val) = (E.entry j i).val
    exact congrArg (fun a : Algebra M => a.val) (E.star_entry i j)
  mul_entry i j k l := by
    apply Subtype.ext
    simpa only [MulMemClass.coe_mul, apply_ite, ZeroMemClass.coe_zero] using
      congrArg (fun a : Algebra M => a.val) (E.mul_entry i j k l)
  total := by
    apply Subtype.ext
    simpa only [AddSubmonoidClass.coe_finsetSum, OneMemClass.coe_one] using
      congrArg (fun a : Algebra M => a.val) E.total

omit [Nontrivial H] [Nonempty ι] in

theorem concreteMatrixUnits_hom (E : MatrixUnitSystem ι (Algebra M))
    (a : Matrix ι ι ℂ) :
    ((concreteMatrixUnits E).hom a).val = E.concreteHom a := by
  change (matrixUnitConcreteAlgebra E).toStarSubalgebra.subtype
    ((concreteMatrixUnits E).hom a) = M.toStarSubalgebra.subtype (E.hom a)
  simp only [MatrixUnitSystem.hom_apply, map_sum, map_smul]
  rfl

omit [Nontrivial H] [Nonempty ι] in
theorem concreteMatrixUnits_surjective (E : MatrixUnitSystem ι (Algebra M)) :
    Function.Surjective (concreteMatrixUnits E).hom := by
  intro x
  obtain ⟨a,ha⟩ := x.property
  refine ⟨a, Subtype.ext ?_⟩
  exact (concreteMatrixUnits_hom E a).trans ha

/-- No injectivity assumption is needed for any finite matrix stage. -/
theorem isInjective_matrixUnitConcreteAlgebra (E : MatrixUnitSystem ι (Algebra M)) :
    IsInjective (matrixUnitConcreteAlgebra E) :=
  isInjective_of_matrixUnits_surjective (concreteMatrixUnits E)
    (concreteMatrixUnits_surjective E)

omit [Nontrivial H] in
/-- The zero Hilbert space causes no exception to stage injectivity. -/
theorem isInjective_matrixUnitConcreteAlgebra_all
    (E : MatrixUnitSystem ι (Algebra M)) : IsInjective (matrixUnitConcreteAlgebra E) := by
  rcases subsingleton_or_nontrivial H with h | h
  · let := h
    refine ⟨0, by simp, ?_, ?_⟩
    · intro x
      simp
    · intro x hx
      exact Subsingleton.elim _ _
  · let := h
    exact isInjective_matrixUnitConcreteAlgebra E

end

end KadisonKastler

end OAI
