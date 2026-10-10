import OAI.Analysis.Pureness.GroupAlgebra.FreeGroupFirstLetter
import OAI.Analysis.Pureness.GroupAlgebra.GroupCoordinateProjection
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Tactic.NoncommRing

namespace OAI
noncomputable section
namespace CuntzPureness
local instance freeGroupPartialTranslationsDecidableEq {X : Type*} : DecidableEq X :=
  Classical.decEq X
variable {X : Type*}

def freeLetterProjection (i : X) (b : Bool) : GroupOperator (FreeGroup X) :=
  groupCoordinateProjection (FreeGroup.startsWith (i, b))

lemma freeLetterProjection_isProjection (i : X) (b : Bool) :
    IsStarProjection (freeLetterProjection i b) := by
  refine ⟨?_, groupCoordinateProjection_star _⟩
  change groupCoordinateProjection _ * groupCoordinateProjection _ = _
  rw [groupCoordinateProjection_mul, Set.inter_self]
  rfl

lemma freeLetterProjection_disjoint (i j : X) (b c : Bool) (h : i ≠ j) :
    freeLetterProjection i b * freeLetterProjection j c = 0 :=
  groupCoordinateProjection_disjoint _ _ (freeGroup_firstLetter_disjoint i j b c h)

lemma freeLetterProjection_vacuum (i : X) (b : Bool) :
    freeLetterProjection i b (groupVacuum (G := FreeGroup X)) = 0 := by
  classical
  ext g
  change (if g ∈ FreeGroup.startsWith (i, b) then groupVacuum g else 0) = 0
  by_cases hg : g = 1
  · subst g
    simp [freeGroup_one_not_firstLetter]
  · simp [groupVacuum, lp.single_apply, hg]

lemma freeLetterProjection_conjugate (i : X) :
    groupLeft (FreeGroup.of i) * (1 - freeLetterProjection i false) *
      star (groupLeft (FreeGroup.of i)) = freeLetterProjection i true := by
  change groupLeft (FreeGroup.mk [(i, true)]) *
    (1 - groupCoordinateProjection (FreeGroup.startsWith (i, false))) *
      star (groupLeft (FreeGroup.mk [(i, true)])) = _
  rw [← groupCoordinateProjection_compl, groupCoordinateProjection_conjugate]
  have hh := freeGroup_firstLetter_image (i, true)
  simp only [Bool.not_true] at hh
  rw [hh]
  rfl

def freeCreation (i : X) : GroupOperator (FreeGroup X) :=
  groupLeft (FreeGroup.of i) * (1 - freeLetterProjection i false)

def freeCancellation (i : X) : GroupOperator (FreeGroup X) :=
  groupLeft (FreeGroup.of i) * freeLetterProjection i false

lemma freeTranslation_split (i : X) :
    freeCreation i + freeCancellation i = groupLeft (FreeGroup.of i) := by
  simp [freeCreation, freeCancellation, mul_sub]

lemma freeCreation_star_mul (i : X) :
    star (freeCreation i) * freeCreation i = 1 - freeLetterProjection i false := by
  have hp := (freeLetterProjection_isProjection i false).one_sub
  simp only [freeCreation, star_mul, hp.isSelfAdjoint.star_eq]
  calc
    _ = (1 - freeLetterProjection i false) *
      (star (groupLeft (FreeGroup.of i)) * groupLeft (FreeGroup.of i)) *
        (1 - freeLetterProjection i false) := by simp only [mul_assoc]
    _ = _ := by simp only [groupLeft_star, ← groupLeft_mul, inv_mul_cancel,
      groupLeft_one, mul_one, hp.isIdempotentElem.eq]

lemma freeCreation_mul_star (i : X) :
    freeCreation i * star (freeCreation i) = freeLetterProjection i true := by
  have hp := (freeLetterProjection_isProjection i false).one_sub
  simp only [freeCreation, star_mul, hp.isSelfAdjoint.star_eq]
  calc
    _ = groupLeft (FreeGroup.of i) *
      ((1 - freeLetterProjection i false) * (1 - freeLetterProjection i false)) *
        star (groupLeft (FreeGroup.of i)) := by simp only [mul_assoc]
    _ = _ := by rw [hp.isIdempotentElem.eq, freeLetterProjection_conjugate]

lemma freeCreation_range (i : X) : freeLetterProjection i true * freeCreation i = freeCreation i := by
  rw [← freeCreation_mul_star, mul_assoc, freeCreation_star_mul]
  dsimp [freeCreation]
  rw [mul_assoc, (freeLetterProjection_isProjection i false).one_sub.isIdempotentElem.eq]

lemma freeCreation_orthogonal (i j : X) (h : i ≠ j) :
    star (freeCreation i) * freeCreation j = 0 := by
  have hleft : star (freeCreation i) * freeLetterProjection i true = star (freeCreation i) := by
    simpa only [star_mul, (freeLetterProjection_isProjection i true).isSelfAdjoint.star_eq]
      using congrArg star (freeCreation_range i)
  calc
    _ = star (freeCreation i) * (freeLetterProjection i true * freeLetterProjection j true) *
        freeCreation j := by rw [← mul_assoc, hleft, mul_assoc, freeCreation_range]
    _ = 0 := by rw [freeLetterProjection_disjoint i j true true h, mul_zero, zero_mul]

lemma freeCancellation_mul_star (i : X) :
    freeCancellation i * star (freeCancellation i) = 1 - freeLetterProjection i true := by
  have hp := freeLetterProjection_isProjection i false
  have hh := freeLetterProjection_conjugate i
  have hu : groupLeft (FreeGroup.of i) * star (groupLeft (FreeGroup.of i)) = 1 := by
    simp [← groupLeft_mul]
  have he : freeCancellation i * star (freeCancellation i) =
      groupLeft (FreeGroup.of i) * freeLetterProjection i false * star (groupLeft (FreeGroup.of i)) := by
    simp only [freeCancellation, star_mul, hp.isSelfAdjoint.star_eq]
    calc
      _ = groupLeft (FreeGroup.of i) * (freeLetterProjection i false * freeLetterProjection i false) *
          star (groupLeft (FreeGroup.of i)) := by simp only [mul_assoc]
      _ = _ := by rw [hp.isIdempotentElem.eq]
  rw [he]
  rw [mul_sub, mul_one, sub_mul, hu] at hh
  exact (sub_eq_iff_eq_add.mp hh).symm |> fun h => by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using h

lemma freeCancellation_orthogonal (i j : X) (h : i ≠ j) :
    freeCancellation i * star (freeCancellation j) = 0 := by
  simp only [freeCancellation, star_mul,
    (freeLetterProjection_isProjection j false).isSelfAdjoint.star_eq]
  calc
    _ = groupLeft (FreeGroup.of i) * (freeLetterProjection i false * freeLetterProjection j false) *
        star (groupLeft (FreeGroup.of j)) := by simp only [mul_assoc]
    _ = 0 := by rw [freeLetterProjection_disjoint i j false false h, mul_zero, zero_mul]

lemma freeCreation_star_vacuum (i : X) :
    star (freeCreation i) (groupVacuum (G := FreeGroup X)) = 0 := by
  have hh := congrArg star (freeCreation_range i)
  simp only [star_mul, (freeLetterProjection_isProjection i true).isSelfAdjoint.star_eq] at hh
  rw [← hh, mul_apply_eq_comp, freeLetterProjection_vacuum, map_zero]
end CuntzPureness

end

end OAI
