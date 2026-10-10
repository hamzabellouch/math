import OAI.Analysis.Pureness.States.FiniteFamilyCompletion
import OAI.Analysis.Pureness.Cuntz.FiniteMatrixCornerNaturality
import OAI.Analysis.Pureness.States.FiniteFamilyBaseCarrier

namespace OAI
noncomputable section
namespace CuntzPureness.CompatibleFiniteQuasitrace
open CuntzTrace
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (F : CompatibleFiniteQuasitrace A)
variable (hmono : ∀ n, Monotone (fun a : Positive (FinMatrix A n) => (F.level n a.1).re))

lemma cauchyInclusion_unit_corner (n : ℕ) :
    F.cauchyInclusion hmono (Nat.zero_le n) 1=F.cauchyEmbedding hmono n (singleMatrix 0 0 (1 : A)) := by
  have he : matrixInclusion (Nat.add_le_add_right (Nat.zero_le n) 1) (1 : FinMatrix A 1)=
      singleMatrix (0 : Fin (n+1)) 0 (1 : A) := by
    have h := matrixInclusion_scalar_one n (1 : A)
    rw [map_one] at h
    exact h
  calc
    _ = F.cauchyInclusion hmono (Nat.zero_le n) (F.cauchyEmbedding hmono 0 1) :=
      congrArg (F.cauchyInclusion hmono (Nat.zero_le n)) (map_one (F.cauchyEmbedding hmono 0)).symm
    _ = _ := by rw [F.cauchyInclusion_embedding,he]

def cauchyMatrixLeg (n : ℕ) (i : Fin n) : F.CauchyLevel hmono n :=
  F.cauchyEmbedding hmono n (singleMatrix i.castSucc 0 (1 : A))

lemma cauchyMatrixLeg_orthogonal (n : ℕ) (i j : Fin n) :
    star (F.cauchyMatrixLeg hmono n i)*F.cauchyMatrixLeg hmono n j=
      if i=j then F.cauchyInclusion hmono (Nat.zero_le n) 1 else 0 := by
  have hs (k : Fin (n+1)) : star (singleMatrix k 0 (1 : A))=singleMatrix 0 k 1 := by
    change CStarMatrix.ofMatrix (Matrix.single k 0 (1 : A)).conjTranspose=
      CStarMatrix.ofMatrix (Matrix.single 0 k 1)
    rw [Matrix.conjTranspose_single,star_one]
  unfold cauchyMatrixLeg
  rw [← map_star,← map_mul,hs]
  by_cases hij : i=j
  · subst j
    rw [ite_eq_left rfl,singleMatrix_mul_same,one_mul]
    exact (F.cauchyInclusion_unit_corner hmono n).symm
  · rw [ite_eq_right hij,singleMatrix_mul_ne _ _ _ _ (fun he => hij (Fin.castSucc_injective n he)),map_zero]

def cauchyMatrixLift (n : ℕ) : FinMatrix (F.CauchyLevel hmono 0) n →⋆ₙₐ[ℂ] F.CauchyLevel hmono n :=
  matrixCornerLift (F.cauchyInclusion hmono (Nat.zero_le n))
    (F.cauchyMatrixLeg hmono n) (F.cauchyMatrixLeg_orthogonal hmono n)

lemma cauchyMatrixLeg_inclusion {n m : ℕ} (h : n ≤ m) (i : Fin n) :
    F.cauchyInclusion hmono h (F.cauchyMatrixLeg hmono n i)=
      F.cauchyMatrixLeg hmono m (Fin.castLE h i) := by
  unfold cauchyMatrixLeg
  rw [F.cauchyInclusion_embedding,matrixInclusion_single]
  rfl

lemma cauchyMatrixLift_inclusion {n m : ℕ} (h : n ≤ m) (M : FinMatrix (F.CauchyLevel hmono 0) n) :
    F.cauchyInclusion hmono h (F.cauchyMatrixLift hmono n M)=
      F.cauchyMatrixLift hmono m (matrixInclusion h M) :=
  matrixCornerLift_inclusion_natural h _ _ _ _ _ _ _
    (F.cauchyInclusion_trans hmono (Nat.zero_le n) h) (F.cauchyMatrixLeg_inclusion hmono h) M

lemma cauchyMatrixLift_scalar_one (x : F.CauchyLevel hmono 0) :
    F.cauchyMatrixLift hmono 1 (scalarMatrixHom (ι := Fin 1) x)=
      F.cauchyInclusion hmono (Nat.zero_le 1) x := by
  have hs : scalarMatrixHom (ι := Fin 1) x=singleMatrix 0 0 x := by
    rw [scalarMatrix_eq_sum_single]
    simp only [Fin.sum_univ_one]
  rw [hs]
  exact matrixCornerLift_first _ _ _ 0 (F.cauchyInclusion_unit_corner hmono 1).symm x

def completedFamily : CompatibleFiniteQuasitrace (F.CauchyLevel hmono 0) where
  level n := (F.cauchyQuasitrace hmono n).comap (F.cauchyMatrixLift hmono n)
  inclusion := by
    intro n m h M
    change F.cauchyQuasitrace hmono m (F.cauchyMatrixLift hmono m (matrixInclusion h M))=
      F.cauchyQuasitrace hmono n (F.cauchyMatrixLift hmono n M)
    rw [F.cauchyQuasitrace_eq,F.cauchyQuasitrace_eq,← F.cauchyMatrixLift_inclusion,
      F.cauchyInclusion_value]

lemma completedFamily_monotone (n : ℕ) :
    Monotone (fun a : Positive (FinMatrix (F.CauchyLevel hmono 0) n) =>
      ((F.completedFamily hmono).level n a.1).re) := by
  intro a b hab
  change ((F.cauchyPositiveQuasitrace hmono n).complexValue (F.cauchyMatrixLift hmono n a.1)).re ≤
    ((F.cauchyPositiveQuasitrace hmono n).complexValue (F.cauchyMatrixLift hmono n b.1)).re
  have h := ((F.cauchyPositiveQuasitrace hmono n).comap (F.cauchyMatrixLift hmono n)).monotone hab
  have ha := (F.cauchyPositiveQuasitrace hmono n).complexValue_positive
    (Positive.map (F.cauchyMatrixLift hmono n) a)
  have hb := (F.cauchyPositiveQuasitrace hmono n).complexValue_positive
    (Positive.map (F.cauchyMatrixLift hmono n) b)
  change (F.cauchyPositiveQuasitrace hmono n).complexValue (F.cauchyMatrixLift hmono n a.1)=_ at ha
  change (F.cauchyPositiveQuasitrace hmono n).complexValue (F.cauchyMatrixLift hmono n b.1)=_ at hb
  rw [ha,hb,Complex.ofReal_re,Complex.ofReal_re]
  exact h

lemma completedFamily_base (x : F.CauchyLevel hmono 0) :
    (F.completedFamily hmono).toTwoQuasitrace.base x=F.cauchyValue hmono 0 x := by
  change F.cauchyQuasitrace hmono 1 (F.cauchyMatrixLift hmono 1 (scalarMatrixHom x))=_
  rw [F.cauchyMatrixLift_scalar_one,F.cauchyQuasitrace_eq,F.cauchyInclusion_value]

lemma completedFamily_unit (hF : F.level 1 1=1) : (F.completedFamily hmono).level 1 1=1 := by
  have h := F.completedFamily_base hmono 1
  change (F.completedFamily hmono).level 1 (scalarMatrixHom 1)=F.cauchyValue hmono 0 1 at h
  rw [map_one] at h
  rw [h,← map_one (F.cauchyEmbedding hmono 0),F.cauchyValue_embedding,hF]
end CuntzPureness.CompatibleFiniteQuasitrace

end

end OAI
