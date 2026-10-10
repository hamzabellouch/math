import OAI.Analysis.Laughlin.FourBody.GroupIntertwining

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix

noncomputable def castSpinColumns {I : Type*} (m n : ℕ) (h : m=n)
    (W : Matrix I (Fin (m+1)) ℂ) : Matrix I (Fin (n+1)) ℂ :=
  fun i j => W i (Fin.cast (congrArg (fun k => k+1) h.symm) j)

theorem castSpinColumns_SU2 {I : Type*} [Fintype I]
    (m n : ℕ) (h : m=n) (W : Matrix I (Fin (m+1)) ℂ)
    (R : Matrix I I ℂ) (g : SourceSU2)
    (hW : R*W=W*sourceSpinRepresentation m g) :
    R*castSpinColumns m n h W = castSpinColumns m n h W*sourceSpinRepresentation n g := by
  subst n
  exact hW

theorem castSpinColumns_isometry {I : Type*} [Fintype I]
    (m n : ℕ) (h : m=n) (W : Matrix I (Fin (m+1)) ℂ) (hW : Wᴴ*W=1) :
    (castSpinColumns m n h W)ᴴ*castSpinColumns m n h W=1 := by
  subst n
  exact hW

def fourSpinWeight (Q D : ℕ) : ℕ := 4*Q-2-2*D

theorem four_nested_weight (Q D r : ℕ) (hQ : D+2 ≤ Q) (hr : r ≤ D) :
    genericCoupledWeight (2*Q-2) (genericCoupledWeight Q Q r) (D-r) = fourSpinWeight Q D := by
  unfold genericCoupledWeight fourSpinWeight
  omega

theorem fourSpinWeight_dimension (Q D : ℕ) (hQ : D+2 ≤ Q) :
    fourSpinWeight Q D+1=4*Q-1-2*D := by unfold fourSpinWeight; omega

noncomputable def retainedFourInclusion (Q D : ℕ) (hQ : D+2 ≤ Q) (r : OddPairLabel D) :
    Matrix (FourWedgeIndex Q) (Fin (fourSpinWeight Q D+1)) ℂ :=
  castSpinColumns _ _ (four_nested_weight Q D (oddPairDeficit r) hQ (oddPairDeficit_le r))
    (fourWedgeInclusion Q (oddPairDeficit r) D
      (by have := oddPairDeficit_le r; omega)
      (by have := oddPairDeficit_le r; omega)
      (by have := oddPairDeficit_le r; unfold genericCoupledWeight; omega))

theorem retainedFourInclusion_column (Q D : ℕ) (hQ : D+2 ≤ Q) (r : OddPairLabel D)
    (n : Fin (fourSpinWeight Q D+1)) (i : FourWedgeIndex Q) :
    retainedFourInclusion Q D hQ r i n =
      (fourBodyCopy Q (oddPairDeficit r) D
        (by have := oddPairDeficit_le r; omega)
        (by have := oddPairDeficit_le r; omega)
        (by have := oddPairDeficit_le r; unfold genericCoupledWeight; omega) n.val i : ℂ) := rfl

theorem retainedFourInclusion_SU2 (Q D : ℕ) (hQ : D+2 ≤ Q) (r : OddPairLabel D)
    (g : SourceSU2) :
    fourBodySpinRepresentation Q g * retainedFourInclusion Q D hQ r =
      retainedFourInclusion Q D hQ r * sourceSpinRepresentation (fourSpinWeight Q D) g := by
  unfold retainedFourInclusion
  apply castSpinColumns_SU2
  exact fourWedgeInclusion_SU2 Q (oddPairDeficit r) D _ (oddPairDeficit_odd r) _ _ g

theorem retainedFourInclusion_isometry (Q D : ℕ) (hQ : D+2 ≤ Q) (r : OddPairLabel D) :
    (retainedFourInclusion Q D hQ r)ᴴ * retainedFourInclusion Q D hQ r = 1 := by
  unfold retainedFourInclusion
  apply castSpinColumns_isometry
  exact fourWedgeInclusion_isometry Q (oddPairDeficit r) D _ (oddPairDeficit_odd r) _ _

end Laughlin.Spin

end OAI
