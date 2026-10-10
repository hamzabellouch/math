import OAI.Analysis.Laughlin.Fock.FourLabels
import OAI.Analysis.Laughlin.FourBody.PhysicalColumn

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

theorem occupationInner_basis_right (Q : ℕ) (x : Space Q) (A : Finset (Fin (Q+1))) :
    occupationInner Q x (occupationBasis Q A) = star ((occupationBasis Q).repr x A) := by
  simp [occupationInner,Module.Basis.repr_self,Finsupp.single_apply]

noncomputable def fourOccupationCoefficient (Q r D : ℕ) (A : Finset (Fin (Q+1))) : ℝ :=
  if hA : A.card=4 then
    if (∑ i ∈ A, i.val)=D+1 then
      let l := occupationFourLabels Q A hA
      Real.sqrt (sourceCopyWeight D r /
        ((l 0).val.factorial*(l 1).val.factorial*(l 2).val.factorial*(l 3).val.factorial : ℝ)) *
        (Certificate.L D r ((l 0).val,(l 1).val,(l 2).val,(l 3).val) : ℝ)
    else 0
  else 0

theorem limitFourColumn_occupation_coefficient (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r)
    (A : Finset (Fin (Q+1))) :
    (occupationBasis Q).repr (limitFourColumn Q r D) A = (fourOccupationCoefficient Q r D A : ℂ) := by
  by_cases hA : A.card=4
  · by_cases hw : (∑ i ∈ A, i.val)=D+1
    · let l := occupationFourLabels Q A hA
      have h := limitFourColumn_physical_L Q r D hr hor (l 0) (l 1) (l 2) (l 3)
        (l.strictMono (by decide)) (l.strictMono (by decide)) (l.strictMono (by decide))
        (by rw [← occupationFourLabels_sum Q A hA]; exact hw)
      rw [← occupationBasis_four Q A hA,occupationInner_basis_right] at h
      have hs := congrArg star h
      simpa [fourOccupationCoefficient,hA,hw,l] using hs
    · rw [limitFourColumn_bidegree Q r D A (Or.inr hw)]
      simp [fourOccupationCoefficient,hA,hw]
  · rw [limitFourColumn_bidegree Q r D A (Or.inl hA)]
    simp [fourOccupationCoefficient,hA]

theorem limitFourColumn_gram_occupation (Q r s D : ℕ) (hr : r ≤ D) (hs : s ≤ D)
    (hor : Odd r) (hos : Odd s) :
    occupationInner Q (limitFourColumn Q r D) (limitFourColumn Q s D) =
      ((∑ A : Finset (Fin (Q+1)), fourOccupationCoefficient Q r D A *
        fourOccupationCoefficient Q s D A : ℝ) : ℂ) := by
  simp [occupationInner,limitFourColumn_occupation_coefficient Q r D hr hor,
    limitFourColumn_occupation_coefficient Q s D hs hos]

end Laughlin.Fock

end OAI
