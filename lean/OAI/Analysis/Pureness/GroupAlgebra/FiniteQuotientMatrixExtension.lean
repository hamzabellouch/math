import OAI.Analysis.Pureness.GroupAlgebra.FiniteQuotientInclusions
import OAI.Analysis.Pureness.States.QuotientMatrixCornerLift
import OAI.Analysis.Pureness.Projections.FiniteSpectralTwoQuasitrace

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped Topology NNReal ENNReal ComplexOrder CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
variable (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
variable (hfinite : ∀ x, d x ≠ ⊤)

def finiteQuotientMatrixLeg (i : Fin 2) : FiniteQuasitraceCauchyQuotient d hd hlsc hfinite 1 :=
  finiteQuasitraceCauchyEmbedding d hd hlsc hfinite 1 (singleMatrix i 0 (1 : A))

lemma finiteQuotientInclusion_unit_corner :
    finiteQuotientInclusion d hd hlsc hfinite (by decide : 0 ≤ 1) 1=
      finiteQuotientMatrixLeg d hd hlsc hfinite 0 := by
  have he := firstMatrixCorner_eq_single (1 : A)
  simp only [firstMatrixCorner,NonUnitalStarAlgHom.comp_apply,StarAlgHom.coe_toNonUnitalStarAlgHom,map_one] at he
  calc
    _ = finiteQuotientInclusion d hd hlsc hfinite (by decide : 0 ≤ 1)
        (finiteQuasitraceCauchyEmbedding d hd hlsc hfinite 0 1) := by
          exact congrArg (finiteQuotientInclusion d hd hlsc hfinite (by decide : 0 ≤ 1))
            (_root_.map_one (finiteQuasitraceCauchyEmbedding d hd hlsc hfinite 0)).symm
    _ = _ := by rw [finiteQuotientInclusion_embedding,he]; rfl

lemma finiteQuotientMatrixLeg_orthogonal (i j : Fin 2) :
    star (finiteQuotientMatrixLeg d hd hlsc hfinite i)*finiteQuotientMatrixLeg d hd hlsc hfinite j=
      if i=j then finiteQuotientInclusion d hd hlsc hfinite (by decide : 0 ≤ 1) 1 else 0 := by
  have hs (k : Fin 2) : star (singleMatrix k 0 (1 : A))=singleMatrix 0 k 1 := by
    change CStarMatrix.ofMatrix (Matrix.single k 0 (1 : A)).conjTranspose=
      CStarMatrix.ofMatrix (Matrix.single 0 k 1)
    rw [Matrix.conjTranspose_single,star_one]
  unfold finiteQuotientMatrixLeg
  rw [← map_star,← map_mul,hs]
  by_cases hij : i=j
  · subst j
    rw [ite_eq_left rfl,singleMatrix_mul_same,one_mul]
    exact (finiteQuotientInclusion_unit_corner d hd hlsc hfinite).symm
  · rw [ite_eq_right hij,singleMatrix_mul_ne _ _ _ _ hij,map_zero]

def finiteQuotientMatrixLift :
    FinMatrix (FiniteQuasitraceCauchyQuotient d hd hlsc hfinite 0) 2 →⋆ₙₐ[ℂ]
      FiniteQuasitraceCauchyQuotient d hd hlsc hfinite 1 :=
  matrixCornerLift (finiteQuotientInclusion d hd hlsc hfinite (by decide : 0 ≤ 1))
    (finiteQuotientMatrixLeg d hd hlsc hfinite) (finiteQuotientMatrixLeg_orthogonal d hd hlsc hfinite)

lemma finiteQuotientMatrixLift_first (x : FiniteQuasitraceCauchyQuotient d hd hlsc hfinite 0) :
    finiteQuotientMatrixLift d hd hlsc hfinite (firstMatrixCorner x)=
      finiteQuotientInclusion d hd hlsc hfinite (by decide : 0 ≤ 1) x := by
  rw [firstMatrixCorner_eq_single]
  exact matrixCornerLift_first _ _ _ 0 (finiteQuotientInclusion_unit_corner d hd hlsc hfinite).symm x

def finiteQuotientTwoQuasitrace : TwoQuasitrace (FiniteQuasitraceCauchyQuotient d hd hlsc hfinite 0) where
  base := finiteQuotientQuasitrace d hd hlsc hfinite 0
  matrix := (((finiteSpectralPositiveQuasitrace d hd hlsc hfinite 2).quotientPositiveQuasitrace
    (finiteSpectralPositiveQuasitrace_metricSize_add d hd hlsc hfinite 2)
    (finiteSpectralPositiveQuasitrace_sqrt_add d hd hlsc hfinite 2)).comap
      (finiteQuotientMatrixLift d hd hlsc hfinite)).toComplex
  extension x := by
    change finiteQuotientQuasitrace d hd hlsc hfinite 0 x=
      (PositiveQuasitrace.comap _ (finiteQuotientMatrixLift d hd hlsc hfinite)).complexValue (firstMatrixCorner x)
    rw [PositiveQuasitrace.comap_complexValue,PositiveQuasitrace.quotientPositiveQuasitrace_complexValue,
      finiteQuotientMatrixLift_first,finiteQuotientQuasitrace_eq]
    exact (finiteQuotientInclusion_value d hd hlsc hfinite (by decide : 0 ≤ 1) x).symm

lemma finiteQuotientTwoQuasitrace_base (x : FiniteQuasitraceCauchyQuotient d hd hlsc hfinite 0) :
    (finiteQuotientTwoQuasitrace d hd hlsc hfinite).base x=finiteQuasitraceCauchyValue d hd hlsc hfinite 0 x :=
  finiteQuotientQuasitrace_eq d hd hlsc hfinite 0 x
end CuntzPureness

end

end OAI
