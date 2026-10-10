import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonGroupoid

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonGroupoidTracks
open Classical CategoryTheory
namespace PolygonObject
variable {a : ℕ}

noncomputable def standard (a m : ℕ) : PolygonObject a := ⟨m,fun _ => ⊤⟩

noncomputable def standardPointEquiv (a m : ℕ) : (standard a m).Point ≃ TrackPoint a m where
  toFun := Subtype.val
  invFun x := ⟨x,by trivial⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def fullGroupArrow {m : ℕ} (g : polygonFullGroup a m) : standard a m ⟶ standard a m where
  toEquiv := (standardPointEquiv a m).trans (g.val.trans (standardPointEquiv a m).symm)
  hasTable := by
    obtain ⟨s,hs,hcover⟩ := g.property
    let conv : TableChart a m → Chart (a:=a) m m := fun c => ⟨c.source,c.target,c.shift,c.domain⟩
    refine ⟨s.image conv,?_,?_⟩
    · intro c hc
      obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
      intro x hx
      refine ⟨by trivial,?_⟩
      exact hs d hd x hx
    · intro x
      obtain ⟨c,hc,hx⟩ := hcover x.val
      exact ⟨conv c,Finset.mem_image.mpr ⟨c,hc,rfl⟩,hx⟩

noncomputable def fullGroupOfArrow {m : ℕ} (g : standard a m ⟶ standard a m) : polygonFullGroup a m :=
  ⟨(standardPointEquiv a m).symm.trans (g.toEquiv.trans (standardPointEquiv a m)),by
    obtain ⟨s,hs,hcover⟩ := g.hasTable
    let conv : Chart (a:=a) m m → TableChart a m := fun c => ⟨c.source,c.target,c.shift,c.domain⟩
    refine ⟨s.image conv,?_,?_⟩
    · intro c hc
      obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
      intro x hx
      obtain ⟨hu,he⟩ := hs d hd x hx
      exact he
    · intro x
      obtain ⟨c,hc,hx⟩ := hcover ((standardPointEquiv _ _).symm x)
      exact ⟨conv c,Finset.mem_image.mpr ⟨c,hc,rfl⟩,hx⟩⟩

@[simp] theorem arrow_fullGroup {m : ℕ} (g : standard a m ⟶ standard a m) :
    fullGroupArrow (fullGroupOfArrow g)=g := by
  apply Arrow.ext
  apply Equiv.ext
  intro x
  rfl

@[simp] theorem fullGroup_arrow {m : ℕ} (g : polygonFullGroup a m) :
    fullGroupOfArrow (fullGroupArrow g)=g := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  rfl

theorem fullGroupArrow_injective {m : ℕ} : Function.Injective (@fullGroupArrow a m) := by
  intro g h he
  simpa using congrArg fullGroupOfArrow he

theorem fullGroupOfArrow_injective {m : ℕ} : Function.Injective (@fullGroupOfArrow a m) := by
  intro g h he
  simpa using congrArg fullGroupArrow he

noncomputable def standardAutEquiv (a m : ℕ) : Aut (standard a m) ≃* polygonFullGroup a m where
  toFun g := fullGroupOfArrow g.hom
  invFun g := asIso (fullGroupArrow g)
  left_inv g := by apply Iso.ext; exact arrow_fullGroup g.hom
  right_inv g := fullGroup_arrow g
  map_mul' g h := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rfl

end PolygonObject
end PolygonGroupoidTracks

end SimpleAmenable
end
end

end OAI
