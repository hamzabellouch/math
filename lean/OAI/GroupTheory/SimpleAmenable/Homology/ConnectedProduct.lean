import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.TensorSplit
import OAI.GroupTheory.SimpleAmenable.Simplicial.SimplicialAugment

namespace OAI

section

section
open CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite AlgebraicTopology
namespace ConnectedProduct
open FreeChains AugmentedSplit

variable (X : SSet) [X.IsConnected]
noncomputable def point : X.obj (op ⦋0⦌) := Classical.arbitrary _
lemma reduced_zero : IsZero ((red (SimplicialAugment.aug X)).homology 0) := by
  let e := SimplicialAugment.aug X
  let s := SimplicialAugment.sec X (point X)
  have hs : s ≫ e=𝟙 U := SimplicialAugment.section_aug X _
  have h : homologyMap (kernel.ι e) 0 = 0 := by
    apply (cancel_mono (homologyMap e 0)).mp
    rw [←homologyMap_comp,kernel.condition,homologyMap_zero,Limits.zero_comp]
  apply (IsZero.iff_id_eq_zero _).mpr
  have hsplit := congrArg (fun f => homologyMap f 0) (splitting e s hs).f_r
  change homologyMap (sc e).f 0 = 0 at h
  rw [homologyMap_comp,homologyMap_id,h,Limits.zero_comp] at hsplit
  exact hsplit.symm
variable (Y : SSet) [Y.IsConnected]
noncomputable def additiveIso (a b n : ℕ) (hn : 0<n) (hab : n<a+b)
    (hX : ∀ i, 0 < i → i < a → IsZero ((complex X).homology i))
    (hY : ∀ i, 0 < i → i < b → IsZero ((complex Y).homology i))
    (hf : ∀ i,i≤n → Module.Finite ℤ ((complex Y).homology i)) :
    SSet.homology (EilenbergZilber.diag ⋙ ProductChains.product X Y) Z n ≅
      X.homology Z n ⊞ Y.homology Z n := by
  let e := SimplicialAugment.aug X
  let s := SimplicialAugment.sec X (point X)
  have hs := SimplicialAugment.section_aug X (point X)
  let f := SimplicialAugment.aug Y
  let t := SimplicialAugment.sec Y (point Y)
  have ht := SimplicialAugment.section_aug Y (point Y)
  exact ProductChains.homologyIso X Y n ≪≫
    TensorSplit.additiveIso e s hs f t ht a b n hn hab
      (AugmentedSplit.vanishing e s hs a (reduced_zero X) hX)
      (AugmentedSplit.vanishing f t ht b (reduced_zero Y) hY) hf ≪≫
    biprod.mapIso ((homologyFunctor _ c n).mapIso (complexIso X)).symm
      ((homologyFunctor _ c n).mapIso (complexIso Y)).symm
end ConnectedProduct

end

end

end OAI
