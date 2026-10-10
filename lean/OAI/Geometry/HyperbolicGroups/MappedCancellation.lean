import Mathlib
import OAI.Geometry.HyperbolicGroups.DipoleChain

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D I L V A : Type*} [DecidableEq D] [Fintype D] [Fintype I]
  [AddCommMonoid A]
namespace PictureMap

/-- Two opposite
face occurrences sharing one indexed side are removed. The number of faces
falls by exactly two, genus zero is retained, the target map on every surviving
side is unchanged, and the exact lifted cellular chain is unchanged. -/
theorem cancel_mapped_dipole (M : PictureMap D) {q : Perm I} {a b : I → D}
    (hF : OppositeFaces M.face q a b) (i₀ : I) (hseed : M.edge (a i₀) = b i₀)
    {label : D → L} {start : L → V} {rev : L → L}
    (hM : M.Respects label start rev) (hG : M.GenusZero)
    (hinv : ∀ l, rev (rev l) = l) (hop : ∀ i, label (b i) = rev (label (a i)))
    (w : D → A) (hw : ∀ x, w (M.face x) = w x) (hchain : w (a i₀) + w (b i₀) = 0) :
    ∃ R : PictureMap {x : D // ¬ InDipole a b x},
      R.GenusZero ∧ R.Respects (label ∘ Subtype.val) start rev ∧
      (∀ x, (R.face x).val = M.face x.val) ∧
      cycles R.face = cycles M.face - 2 ∧
      ∃ hR : ∀ x, (w ∘ Subtype.val) (R.face x) = (w ∘ Subtype.val) x,
        faceChain R.face (w ∘ Subtype.val) hR = faceChain M.face w hw := by
  classical
  obtain ⟨N,hf,hn,hng,_,hp⟩ := M.isolate_dipole hF i₀ hseed hM hG hinv hop
  have hfn : OppositeFaces N.face q a b := by rw [hf]; exact hF
  have hwn : ∀ x, w (N.face x) = w x := by rw [hf]; exact hw
  let R := N.removeDipole hfn hp
  refine ⟨R,?_,?_,?_,?_,?_⟩
  · convert N.removeDipole_genusZero hfn hp hng using 1
  · exact N.restrict_respects hn _ _ _
  · intro x
    change N.face x.val = M.face x.val
    rw [hf]
  · convert N.removeDipole_faces hfn hp i₀ using 1
    rw [hf]
  · refine ⟨fun x => hwn x.val,?_⟩
    have hh := N.removeDipole_chain hfn hp i₀ w hwn hchain
    convert hh using 1
    simp only [hf]

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
