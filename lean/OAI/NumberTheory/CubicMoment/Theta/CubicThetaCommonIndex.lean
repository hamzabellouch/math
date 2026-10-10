import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCommonSupport
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryIndex

namespace OAI

/-! The actual dual support is indexed once by its unit, ramified order,
squarefree primary factor and primary cube factor. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

abbrev CubicThetaCommonIndex := Eisensteinˣ × ℕ × CubicThetaPrimaryPair

def cubicThetaCommonNumerator (x : CubicThetaCommonIndex) : Eisenstein :=
  (x.1:Eisenstein)*lambdaE^x.2.1*(x.2.2.val.1*x.2.2.val.2^3)

def cubicThetaCommonCoordinates (x : CubicThetaCommonIndex) :
    CubicThetaCoordinates (cubicThetaCommonNumerator x) where
  unit := x.1
  order := x.2.1
  squarefreePart := x.2.2.val.1
  cubePart := x.2.2.val.2
  squarefree_primary := x.2.2.property.1
  cube_primary := x.2.2.property.2.1
  squarefree := x.2.2.property.2.2
  numerator_eq := rfl

lemma cubicThetaCommonNumerator_injective : Function.Injective cubicThetaCommonNumerator := by
  rintro ⟨u,k,cd⟩ ⟨v,l,ef⟩ he
  have hp (x : CubicThetaPrimaryPair) : primary (x.val.1*x.val.2^3) :=
    primary_mul x.property.1 (by
      simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using
        primary_mul x.property.2.1 (primary_mul x.property.2.1 x.property.2.1))
  have h := unit_ramified_primary_unique (hp cd) (hp ef) he
  have hc := primary_squarefree_cube_unique cd.property.1 cd.property.2.1
    ef.property.1 ef.property.2.1 cd.property.2.2 ef.property.2.2 h.2.2
  have hcd : cd=ef := Subtype.ext (Prod.ext hc.1 hc.2)
  exact Prod.ext h.1 (Prod.ext h.2.1 hcd)

lemma cubicThetaCommonNumerator_range (n : Eisenstein) :
    n∈Set.range cubicThetaCommonNumerator ↔ Nonempty (CubicThetaCoordinates n) := by
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨cubicThetaCommonCoordinates x⟩
  · rintro ⟨R⟩
    refine ⟨(R.unit,R.order,⟨(R.squarefreePart,R.cubePart),
      R.squarefree_primary,R.cube_primary,R.squarefree⟩),?_⟩
    exact R.numerator_eq.symm

theorem cubicThetaCommon_tsum (f : Eisenstein→ℂ)
    (hf : Function.support f⊆{n | Nonempty (CubicThetaCoordinates n)}) :
    (∑' n : Eisenstein,f n)=∑' x : CubicThetaCommonIndex,f (cubicThetaCommonNumerator x) := by
  exact (cubicThetaCommonNumerator_injective.tsum_eq (fun n hn =>
    (cubicThetaCommonNumerator_range n).mpr (hf hn))).symm

theorem cubicThetaCommon_weighted_tsum (f : Eisenstein→ℂ) :
    (∑' n : MetaplecticDualArgument,cubicThetaCommonCuspCoefficient n.val*f n.val)=
      ∑' x : CubicThetaCommonIndex,
        cubicThetaCommonCuspCoefficient (cubicThetaCommonNumerator x)*f (cubicThetaCommonNumerator x) := by
  let F (n : Eisenstein) : ℂ := if n=0 then 0 else cubicThetaCommonCuspCoefficient n*f n
  have hF : Function.support F⊆{n | Nonempty (CubicThetaCoordinates n)} := by
    intro n hn
    have hn0 : n≠0 := by intro h; exact hn (by simp [F,h])
    have hc : cubicThetaCommonCuspCoefficient n≠0 := by
      intro h
      exact hn (by simp [F,h])
    exact cubicThetaCommonCuspCoefficient_support hn0 hc
  calc
    _ = ∑' n : Eisenstein,F n := by
      have hs : Function.support F⊆{n | n≠0} := by
        intro n hn h
        exact hn (by simp [F,h])
      rw [←tsum_subtype_eq_of_support_subset hs]
      apply tsum_congr
      intro n
      simp only [F,ite_eq_right n.property]
    _ = ∑' x : CubicThetaCommonIndex,F (cubicThetaCommonNumerator x) :=
      cubicThetaCommon_tsum F hF
    _ = _ := by
      apply tsum_congr
      intro x
      exact ite_eq_right (cubicThetaCommonCoordinates x).ne_zero

end CubicFirstMoment

end

end OAI
