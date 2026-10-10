import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PlanePeriodization

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PeriodizationCovariance

open Classical
namespace SquareStep
variable {a : ℕ}

theorem periodize_translate (f : PlaneStep a) (u : CutRing × CutRing) :
    periodize (PlaneStep.translate u f)=translate u (periodize f) := by
  apply Subtype.ext
  funext p
  simp only [translate_apply, periodize_apply]
  let k : ℤ×ℤ := (⌊p.val.1-ordinary u.1⌋,⌊p.val.2-ordinary u.2⌋)
  calc
    (∑ᶠ n : ℤ×ℤ, (slice n (PlaneStep.translate u f)).val p) =
        ∑ᶠ n : ℤ×ℤ, (slice (n+k) f).val (SimpleAmenable.translate a (-u) p) := by
      apply finsum_congr
      intro n
      simp only [slice_apply,PlaneStep.translate_apply]
      apply congrArg f.val
      apply Subtype.ext
      simp only [GenericPlane.shift,SimpleAmenable.translate_val,intPair,Prod.fst_add,Prod.snd_add,
        Prod.fst_neg,Prod.snd_neg,map_neg,map_intCast,Int.cast_add,Int.fract]
      dsimp [k]
      ext <;> simp only [Prod.fst_add,Prod.snd_add,Int.fract,map_add,map_intCast] <;> ring_nf
    _ = _ := finsum_comp_equiv (Equiv.addRight k)
      (f := fun n => (slice n f).val (SimpleAmenable.translate a (-u) p))

noncomputable def orbitProjection : Multiplicative (CutRing × CutRing) →*
    Multiplicative (ℤ×ℤ) where
  toFun u := Multiplicative.ofAdd (u.toAdd.1.im,u.toAdd.2.im)
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def orbitLift : Multiplicative (ℤ×ℤ) →*
    Multiplicative (CutRing × CutRing) where
  toFun n := Multiplicative.ofAdd ((n.toAdd.1:CutRing)*cutTau,(n.toAdd.2:CutRing)*cutTau)
  map_one' := by ext <;> simp
  map_mul' n m := by
    change Multiplicative.ofAdd
      (((n.toAdd.1+m.toAdd.1:ℤ):CutRing)*cutTau,((n.toAdd.2+m.toAdd.2:ℤ):CutRing)*cutTau) =
        Multiplicative.ofAdd (((n.toAdd.1:CutRing)*cutTau,(n.toAdd.2:CutRing)*cutTau) +
          ((m.toAdd.1:CutRing)*cutTau,(m.toAdd.2:CutRing)*cutTau))
    congr 1
    ext <;> simp [add_mul]

noncomputable def orbitRepresentation (a : ℕ) :
    Representation ℤ (Multiplicative (ℤ×ℤ)) (SquareStep a) :=
  (representation a).comp orbitLift

theorem representation_reduce (u : Multiplicative (CutRing × CutRing)) :
    representation a u = orbitRepresentation a (orbitProjection u) := by
  ext f p
  change f.val (SimpleAmenable.translate a (-u.toAdd) p) =
    f.val (SimpleAmenable.translate a (-((u.toAdd.1.im:CutRing)*cutTau,
      (u.toAdd.2.im:CutRing)*cutTau)) p)
  have he := translation_reduce a (-u.toAdd)
  have he' := Equiv.congr_fun he p
  simpa only [translation_apply,Prod.fst_neg,Prod.snd_neg,QuadraticAlgebra.im_neg,
    Int.cast_neg,neg_mul,Prod.neg_mk] using congrArg f.val he'

end SquareStep
end PeriodizationCovariance

end SimpleAmenable
end
end

end OAI
