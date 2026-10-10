import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCommonIndex
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFreeCubeParts

namespace OAI

/-! An exact bijection separating every primary cube factor into the
part supported on the level and the free part. No multiplicity is lost. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

abbrev CubicThetaCoreIndex (r : Eisenstein) :=
  {x : CubicThetaCommonIndex // ∃ k : ℕ, x.2.2.val.2∣r^k}
abbrev CubicThetaFreeArgument (r : Eisenstein) :=
  {d : PrimaryArgument // IsCoprime (d:Eisenstein) r}

def cubicThetaFreeCubeJoin (r : Eisenstein)
    (x : CubicThetaCoreIndex r × CubicThetaFreeArgument r) : CubicThetaCommonIndex :=
  (x.1.val.1,x.1.val.2.1,⟨(x.1.val.2.2.val.1,x.1.val.2.2.val.2*(x.2.val:Eisenstein)),
    x.1.val.2.2.property.1,
    primary_mul x.1.val.2.2.property.2.1 x.2.val.property,
    x.1.val.2.2.property.2.2⟩)

lemma cubicThetaFreeCubeJoin_injective {r : Eisenstein} (hr : r≠0) :
    Function.Injective (cubicThetaFreeCubeJoin r) := by
  intro a b he
  have hu := congrArg (fun x : CubicThetaCommonIndex => x.1) he
  have hk := congrArg (fun x : CubicThetaCommonIndex => x.2.1) he
  have hc := congrArg (fun x : CubicThetaCommonIndex => x.2.2.val.1) he
  have hd := congrArg (fun x : CubicThetaCommonIndex => x.2.2.val.2) he
  change a.1.val.1=b.1.val.1 at hu
  change a.1.val.2.1=b.1.val.2.1 at hk
  change a.1.val.2.2.val.1=b.1.val.2.2.val.1 at hc
  change a.1.val.2.2.val.2*(a.2.val:Eisenstein)=
    b.1.val.2.2.val.2*(b.2.val:Eisenstein) at hd
  have hs := cubicTheta_supported_free_unique hr a.1.val.2.2.property.2.1 a.2.val.property
    b.1.val.2.2.property.2.1 b.2.val.property a.1.property b.1.property
    a.2.property b.2.property hd
  exact Prod.ext (Subtype.ext (Prod.ext hu (Prod.ext hk (Subtype.ext (Prod.ext hc hs.1)))))
    (Subtype.ext (Subtype.ext hs.2))

lemma cubicThetaFreeCubeJoin_surjective {r : Eisenstein} (hr : r≠0) :
    Function.Surjective (cubicThetaFreeCubeJoin r) := by
  intro x
  let c := x.2.2.val.1
  let d := x.2.2.val.2
  have hd : primary d := x.2.2.property.2.1
  let y : CubicThetaCoreIndex r := ⟨(x.1,x.2.1,
    ⟨(c,primarySmallPart r d),x.2.2.property.1,primarySmallPart_primary r hd,
      x.2.2.property.2.2⟩),cubicTheta_primarySmallPart_supported hr hd⟩
  let e : CubicThetaFreeArgument r :=
    ⟨⟨primaryOutsidePart r d,primaryOutsidePart_primary r hd⟩,primaryOutsidePart_coprime hd hr⟩
  refine ⟨(y,e),?_⟩
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact primary_small_outside_mul r hd

def cubicThetaFreeCubeEquiv (r : Eisenstein) (hr : r≠0) :
    (CubicThetaCoreIndex r × CubicThetaFreeArgument r) ≃ CubicThetaCommonIndex :=
  Equiv.ofBijective (cubicThetaFreeCubeJoin r)
    ⟨cubicThetaFreeCubeJoin_injective hr,cubicThetaFreeCubeJoin_surjective hr⟩

theorem cubicTheta_free_cube_tsum {r : Eisenstein} (hr : r≠0)
    (f : CubicThetaCommonIndex→ℂ) :
    (∑' x : CubicThetaCommonIndex,f x)=
      ∑' x : CubicThetaCoreIndex r × CubicThetaFreeArgument r,f (cubicThetaFreeCubeJoin r x) :=
  ((cubicThetaFreeCubeEquiv r hr).tsum_eq f).symm

end CubicFirstMoment

end

end OAI
