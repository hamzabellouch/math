import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCubeCancellation
import OAI.NumberTheory.CubicMoment.Estimates.SmallPrimeParts

namespace OAI

/-! Canonical removal of the free primary cube. The remaining cube part
is supported on the level, and the removed factor is coprime to it. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicTheta_primarySmallPart_supported {r a : Eisenstein} (hr : r≠0)
    (_ha : primary a) : ∃ k : ℕ, primarySmallPart r a∣r^k := by
  let ν := supportedIdealPart r (idealExponentOf a)
  let k := ν.support.sup ν
  have hle : ν≤k•idealExponentOf r := by
    intro p
    change ν p≤k*idealExponentOf r p
    by_cases hp : ν p=0
    · rw [hp]
      exact Nat.zero_le _
    · have hpm : p∈ν.support := Finsupp.mem_support_iff.mpr hp
      have hpr : idealExponentOf r p≠0 := by
        intro hz
        exact hp (by simp [ν,supportedIdealPart,hz])
      exact (Finset.le_sup hpm).trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hpr))
  refine ⟨k,?_⟩
  change primaryNormalize (idealExponentGenerator ν)∣r^k
  have hd := idealExponentGenerator_dvd_of_le hle
  have he : k•idealExponentOf r=idealExponentOf (r^k) := (idealExponentOf_pow hr k).symm
  rw [he] at hd
  exact (primaryNormalize_associated _).symm.dvd.trans
    (hd.trans (idealExponentOf_associated (pow_ne_zero _ hr)).dvd)

def CubicThetaCoordinates.coreNumerator {n : Eisenstein} (R : CubicThetaCoordinates n)
    (r : Eisenstein) : Eisenstein :=
  (R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*(primarySmallPart r R.cubePart)^3)

def CubicThetaCoordinates.core {n : Eisenstein} (R : CubicThetaCoordinates n)
    (r : Eisenstein) : CubicThetaCoordinates (R.coreNumerator r) where
  unit := R.unit
  order := R.order
  squarefreePart := R.squarefreePart
  cubePart := primarySmallPart r R.cubePart
  squarefree_primary := R.squarefree_primary
  cube_primary := primarySmallPart_primary r R.cube_primary
  squarefree := R.squarefree
  numerator_eq := rfl

lemma CubicThetaCoordinates.core_decomposition {n : Eisenstein}
    (R : CubicThetaCoordinates n) (r : Eisenstein) :
    n=R.coreNumerator r*(primaryOutsidePart r R.cubePart)^3 := by
  conv_lhs => rw [R.numerator_eq,←primary_small_outside_mul r R.cube_primary]
  unfold coreNumerator
  ring

lemma CubicThetaCoordinates.core_cube_supported {n : Eisenstein}
    (R : CubicThetaCoordinates n) {r : Eisenstein} (hr : r≠0) :
    ∃ k : ℕ, (R.core r).cubePart∣r^k :=
  cubicTheta_primarySmallPart_supported hr R.cube_primary

lemma CubicThetaCoordinates.free_cube_coprime {n : Eisenstein}
    (R : CubicThetaCoordinates n) {r : Eisenstein} (hr : r≠0) :
    IsCoprime (primaryOutsidePart r R.cubePart) r :=
  primaryOutsidePart_coprime R.cube_primary hr

theorem CubicThetaCoordinates.common_coefficient_core {n : Eisenstein}
    (R : CubicThetaCoordinates n) (r : Eisenstein) :
    cubicThetaCommonCuspCoefficient n=
      (norm (primaryOutsidePart r R.cubePart):ℂ)⁻¹*
        cubicThetaCommonCuspCoefficient (R.coreNumerator r) := by
  conv_lhs => rw [R.core_decomposition r]
  exact cubicThetaCommonCuspCoefficient_primaryCube _
    (primaryOutsidePart_primary r R.cube_primary) _

theorem CubicThetaCoordinates.common_tau_core {n : Eisenstein}
    (R : CubicThetaCoordinates n) (r : Eisenstein) :
    cubicThetaCommonTau n=
      (Real.sqrt (norm (primaryOutsidePart r R.cubePart)):ℂ)*
        cubicThetaCommonTau (R.coreNumerator r) := by
  conv_lhs => rw [R.core_decomposition r]
  exact cubicThetaCommonTau_cube _ (primaryOutsidePart_primary r R.cube_primary) _

end CubicFirstMoment

end

end OAI
