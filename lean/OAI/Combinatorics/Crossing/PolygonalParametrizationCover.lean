import OAI.Combinatorics.Crossing.OrderedKnotCover

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem PolygonalParametrization.hasFiniteAffineCover {a b : Plane} {γ : Path a b}
    (P : PolygonalParametrization γ) : HasFiniteAffineCover γ := by
  classical
  let f : Fin P.pieces → unitInterval × unitInterval := fun i => (P.knot i.castSucc,P.knot i.succ)
  refine ⟨Finset.univ.image f,?_,?_,?_⟩
  · intro ab hab
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hab
    exact P.increasing (by change i.val < i.val+1; omega)
  · intro t
    obtain ⟨i,hi,hj⟩ := P.knot_cover t
    exact ⟨f i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,hi,hj⟩
  · intro ab hab t
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hab
    exact P.affine i t

end Zarankiewicz

end

end OAI
