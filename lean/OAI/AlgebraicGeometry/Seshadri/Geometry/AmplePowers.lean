import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.PowerExtension

namespace OAI


                                     
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

theorem LineBundle.IsAmple.pow {L : LineBundle X} (hL : L.IsAmple) (d : ℕ) (hd : 0 < d) :
    (L.pow d).IsAmple := by
  intro x V hx
  obtain ⟨n,hn,s,hs,hsub,ha⟩ := hL x V hx
  let e : ((L.pow n).pow d).sheaf ≅ ((L.pow d).pow n).sheaf :=
    linePowerMul L n d ≪≫ eqToIso (congrArg (fun j => (L.pow j).sheaf) (Nat.mul_comm n d)) ≪≫
      (linePowerMul L d n).symm
  let t := powerSection s d ≫ e.hom
  have ht : sectionOpen X t = sectionOpen X s := by
    change SectionOpens.isoOpen (powerSection s d ≫ e.hom) = _
    erw [SectionOpens.isoOpen_postcomp]
    exact (L.pow n).sectionOpen_power s hd
  refine ⟨n,hn,t,?_,?_,?_⟩ <;> (erw [ht]; assumption)

end
end MaximalSeshadri.Geometry

end


end OAI
