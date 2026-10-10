import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoreCoefficient
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFreeCubeIndex
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFreeLocalVoronoi

namespace OAI

/-! The supported core indices and free primary factors give exactly the
nonzero domain of the full dual sum, with all zero extensions retained. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaCoreArgument {r : Eisenstein} (x : CubicThetaCoreIndex r) : MetaplecticDualArgument :=
  cubicThetaCommonArgument x.val

lemma cubicThetaCoreArgument_injective (r : Eisenstein) :
    Function.Injective (cubicThetaCoreArgument (r:=r)) := by
  intro x y he
  exact Subtype.ext (cubicThetaCommonArgument_injective he)

lemma cubicThetaCoreArgument_range (r : Eisenstein) (n : MetaplecticDualArgument) :
    n∈Set.range (cubicThetaCoreArgument (r:=r)) ↔ CubicThetaCoreSupport r n := by
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨cubicThetaCommonCoordinates x.val,x.property⟩
  · rintro ⟨R,k,hk⟩
    let x : CubicThetaCoreIndex r := ⟨(R.unit,R.order,
      ⟨(R.squarefreePart,R.cubePart),R.squarefree_primary,R.cube_primary,R.squarefree⟩),k,hk⟩
    exact ⟨x,Subtype.ext R.numerator_eq.symm⟩

def cubicThetaCoreFreeArgument (r : Eisenstein)
    (x : CubicThetaCoreIndex r × CubicThetaFreeArgument r) :
    MetaplecticDualArgument × PrimaryArgument := (cubicThetaCoreArgument x.1,x.2.val)

lemma cubicThetaCoreFreeArgument_injective (r : Eisenstein) :
    Function.Injective (cubicThetaCoreFreeArgument r) := by
  intro x y he
  exact Prod.ext (cubicThetaCoreArgument_injective r (congrArg Prod.fst he))
    (Subtype.ext (congrArg Prod.snd he))

theorem cubicTheta_core_free_tsum (r : Eisenstein)
    (f : MetaplecticDualArgument × PrimaryArgument→ℂ) :
    (∑' nd : MetaplecticDualArgument × PrimaryArgument,
      if IsCoprime (nd.2:Eisenstein) r then cubicThetaCoreCoefficient r nd.1*f nd else 0)=
    ∑' x : CubicThetaCoreIndex r × CubicThetaFreeArgument r,
      cubicThetaCoreCoefficient r (cubicThetaCoreArgument x.1)*f (cubicThetaCoreFreeArgument r x) := by
  let F (nd : MetaplecticDualArgument × PrimaryArgument) : ℂ :=
    if IsCoprime (nd.2:Eisenstein) r then cubicThetaCoreCoefficient r nd.1*f nd else 0
  have hs : Function.support F⊆Set.range (cubicThetaCoreFreeArgument r) := by
    intro nd hnd
    have hd : IsCoprime (nd.2:Eisenstein) r := by
      by_contra h
      exact hnd (by simp only [F,ite_eq_right h])
    have hn : CubicThetaCoreSupport r nd.1 := by
      by_contra h
      exact hnd (by simp only [F,ite_eq_left hd,cubicThetaCoreCoefficient,ite_eq_right h,zero_mul])
    obtain ⟨x,hx⟩ := (cubicThetaCoreArgument_range r nd.1).mpr hn
    exact ⟨(x,⟨nd.2,hd⟩),Prod.ext hx rfl⟩
  have h := (cubicThetaCoreFreeArgument_injective r).tsum_eq hs
  calc
    _ = ∑' x : CubicThetaCoreIndex r × CubicThetaFreeArgument r,
        F (cubicThetaCoreFreeArgument r x) := h.symm
    _ = _ := by
      apply tsum_congr
      intro x
      exact ite_eq_left x.2.property

end CubicFirstMoment

end

end OAI
