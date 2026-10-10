import OAI.Analysis.Laughlin.ThreeBody.FockHaar
import OAI.Analysis.Laughlin.ThreeBody.NullSectors

namespace OAI

namespace Laughlin.Fock
open Rotation Spin
open scoped BigOperators Matrix

theorem threeBodyColumn_sourceThreeVector (Q : ℕ) (i : PairOrbitalIndex Q) :
    threeBodyColumn Q i.1.val i.2 = sourceThreeVector Q i := by
  rw [threeBodyColumn,sourcePairCreateEnd_mul]
  rfl

theorem threeWedge_contraction_zero (Q : ℕ) (v : PairOrbitalIndex Q → ℂ)
    (hv : threeWedge Q v=0) (x : Space Q) :
    (∑ i, star (v i) • sourceThreeEnd Q i x)=0 := by
  apply occupationInner_ext_right Q
  intro y
  have h : occupationInner Q (threeWedge Q v*y) x =
      occupationInner Q y (∑ i, star (v i) • sourceThreeEnd Q i x) := by
    simp only [threeWedge,Finset.sum_mul,smul_mul_assoc,occupationInner_sum_left,
      occupationInner_smul_left,threeBodyColumn_sourceThreeVector,sourceThreeVector_adjoint,
      occupationInner_sum_right,occupationInner_smul_right]
  rw [← h,hv,zero_mul]
  simp [occupationInner]

theorem physical_threeBody_Fock_null (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1))
    (hz : z.val=0 ∨ z.val=1 ∨ z.val=3) (x : Space Q) :
    contractionForm Q (sourceThreeEnd Q) ((threeSpinProjector Q hQ z).map Complex.ofReal) x = 0 := by
  let R := (threeSpinProjector Q hQ z).map Complex.ofReal
  have hc (j : PairOrbitalIndex Q) : (∑ i, star (R i j) • sourceThreeEnd Q i x)=0 := by
    apply threeWedge_contraction_zero
    have h := source_threeBody_null_sectors Q hQ z hz (Pi.single j 1)
    have he : complexThreeSpinProjector Q hQ z *ᵥ Pi.single j 1 = (fun i => R i j) := by
      funext i
      simp [Matrix.mulVec,dotProduct,Pi.single_apply,complexThreeSpinProjector,R]
    rw [he] at h
    exact h
  have he : contractionForm Q (sourceThreeEnd Q) R x =
      ∑ j, occupationInner Q (∑ i, star (R i j) • sourceThreeEnd Q i x) (sourceThreeEnd Q j x) := by
    simp only [contractionForm,occupationInner_sum_left,occupationInner_smul_left,star_star]
    rw [Finset.sum_comm]
  change contractionForm Q (sourceThreeEnd Q) R x=0
  rw [he]
  simp only [hc]
  simp [occupationInner]

end Laughlin.Fock

end OAI
