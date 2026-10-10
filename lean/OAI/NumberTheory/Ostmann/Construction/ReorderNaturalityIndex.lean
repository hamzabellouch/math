import OAI.NumberTheory.Ostmann.Arithmetic.OccurrencePermutation

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.OccurrencePermutation

theorem indexEquiv_eq_of_get {A : Type*} {xs ys : List A} (h : xs.Perm ys)
    (hy : ys.Nodup) (e : Fin xs.length ≃ Fin ys.length)
    (he : ∀i,ys.get (e i)=xs.get i) : indexEquiv h=e := by
  apply Equiv.ext
  intro i
  exact hy.injective_get ((get_indexEquiv h i).trans (he i).symm)

theorem indexEquiv_eq_of_key {A B : Type*} {xs ys : List A} (h : xs.Perm ys)
    (key : A→B) (hkey : Function.Injective (fun i => key (ys.get i)))
    (e : Fin xs.length ≃ Fin ys.length)
    (he : ∀i,key (ys.get (e i))=key (xs.get i)) : indexEquiv h=e := by
  apply Equiv.ext
  intro i
  apply hkey
  change key (ys.get (indexEquiv h i))=key (ys.get (e i))
  rw [get_indexEquiv,he]

theorem indexEquiv_naturality {A B : Type*} {xs ys : List A} {xs' ys' : List B}
    (h : xs.Perm ys) (h' : xs'.Perm ys') (hy' : ys'.Nodup)
    (ex : Fin xs.length ≃ Fin xs'.length) (ey : Fin ys.length ≃ Fin ys'.length)
    (hmatch : ∀i j,ys.get j=xs.get i → ys'.get (ey j)=xs'.get (ex i)) :
    (indexEquiv h).trans ey=ex.trans (indexEquiv h') := by
  apply Equiv.ext
  intro i
  apply hy'.injective_get
  exact (hmatch i (indexEquiv h i) (get_indexEquiv h i)).trans (get_indexEquiv h' (ex i)).symm

theorem indexEquiv_naturality_apply {A B : Type*} {xs ys : List A} {xs' ys' : List B}
    (h : xs.Perm ys) (h' : xs'.Perm ys') (hy' : ys'.Nodup)
    (ex : Fin xs.length ≃ Fin xs'.length) (ey : Fin ys.length ≃ Fin ys'.length)
    (hmatch : ∀i j,ys.get j=xs.get i → ys'.get (ey j)=xs'.get (ex i))
    (i : Fin xs.length) : ey (indexEquiv h i)=indexEquiv h' (ex i) :=
  Equiv.congr_fun (indexEquiv_naturality h h' hy' ex ey hmatch) i

theorem indexEquiv_symm_naturality {A B : Type*} {xs ys : List A} {xs' ys' : List B}
    (h : xs.Perm ys) (h' : xs'.Perm ys') (hy' : ys'.Nodup)
    (ex : Fin xs.length ≃ Fin xs'.length) (ey : Fin ys.length ≃ Fin ys'.length)
    (hmatch : ∀i j,ys.get j=xs.get i → ys'.get (ey j)=xs'.get (ex i))
    (j : Fin ys.length) : ex ((indexEquiv h).symm j)=(indexEquiv h').symm (ey j) := by
  apply (indexEquiv h').injective
  simpa only [Equiv.apply_symm_apply] using
    (indexEquiv_naturality_apply h h' hy' ex ey hmatch ((indexEquiv h).symm j)).symm

theorem pullback_naturality {A B U V : Type*} {xs ys : List A} {xs' ys' : List B}
    (h : xs.Perm ys) (h' : xs'.Perm ys') (hy' : ys'.Nodup)
    (ex : Fin xs.length ≃ Fin xs'.length) (ey : Fin ys.length ≃ Fin ys'.length)
    (hmatch : ∀i j,ys.get j=xs.get i → ys'.get (ey j)=xs'.get (ex i))
    (f : Fin xs.length→U) (f' : Fin xs'.length→V) (R : U→V)
    (hf : ∀i,f' (ex i)=R (f i)) (j : Fin ys.length) :
    f' ((indexEquiv h').symm (ey j))=R (f ((indexEquiv h).symm j)) := by
  rw [← indexEquiv_symm_naturality h h' hy' ex ey hmatch]
  exact hf _

theorem get_finCongr_of_map_eq {A B : Type*} (f : A→B) {xs : List A} {ys : List B}
    (he : xs.map f=ys) (hlen : xs.length=ys.length) (i : Fin xs.length) :
    ys.get (finCongr hlen i)=f (xs.get i) := by
  subst ys
  simp [finCongr]

end Ostmann.Arithmetic.OccurrencePermutation

end

end OAI
