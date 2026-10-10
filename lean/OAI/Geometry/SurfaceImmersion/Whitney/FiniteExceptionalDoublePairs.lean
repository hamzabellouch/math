import OAI.Geometry.SurfaceImmersion.Geometry.PreparedSurfaceFiniteFibers

namespace OAI

/-! Only finitely many double pairs involve a point in a prescribed finite set. -/
noncomputable section
open Set Filter Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

lemma finite_exceptional_double_pairs {X Y : Type*} (f : X → Y)
    (hfin : ∀ y, {x | f x = y}.Finite) {S : Set X} (hS : S.Finite) :
    {z : X × X | (z.1 ∈ S ∨ z.2 ∈ S) ∧ f z.1 = f z.2}.Finite := by
  let L : Set (X × X) := ⋃ p ∈ S, (Prod.mk p) '' {q | f q = f p}
  have hL : L.Finite := hS.biUnion (fun p _ => (hfin (f p)).image (Prod.mk p))
  apply (hL.union (hL.image Prod.swap)).subset
  rintro ⟨p,q⟩ ⟨hS,hpq⟩
  rcases hS with hp | hq
  · left
    exact mem_iUnion₂.mpr ⟨p,hp,q,hpq.symm,rfl⟩
  · right
    refine ⟨(q,p),?_,rfl⟩
    exact mem_iUnion₂.mpr ⟨q,hq,p,hpq,rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
