import Mathlib
import OAI.Geometry.HyperbolicGroups.BoundaryList

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D S L : Type*} [DecidableEq D]

/-- A literal indexed match between two enumerated boundaries. Repeated
edge letters are not quotiented: this map uses the unique side positions. -/
def boundaryIndex (xs : List D) (ys : List S) (hlen : xs.length = ys.length)
    (x : D) (hx : x ∈ xs) : S :=
  ys[xs.idxOf x]'(by rw [← hlen]; exact List.idxOf_lt_length_iff.mpr hx)

lemma boundaryIndex_get (xs : List D) (ys : List S) (hn : xs.Nodup)
    (hlen : xs.length = ys.length) (i : ℕ) (hi : i < xs.length) :
    boundaryIndex xs ys hlen xs[i] (List.getElem_mem hi) = ys[i]'(by omega) := by
  have hh : xs.idxOf xs[i] < xs.length := List.idxOf_lt_length_iff.mpr (List.getElem_mem hi)
  have he : xs.idxOf xs[i] = i := hn.getElem_inj_iff.mp (List.getElem_idxOf hh)
  simp only [boundaryIndex,he]

lemma boundaryIndex_label (xs : List D) (ys : List S) (hlen : xs.length = ys.length)
    (label : D → L) (edge : S → L) (he : xs.map label = ys.map edge)
    (x : D) (hx : x ∈ xs) : edge (boundaryIndex xs ys hlen x hx) = label x := by
  have hi : xs.idxOf x < xs.length := List.idxOf_lt_length_iff.mpr hx
  have h := congrArg (fun l => l[xs.idxOf x]?) he
  simp only [List.getElem?_map,List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (show xs.idxOf x < ys.length by omega),Option.map_some,
    Option.some.injEq,List.getElem_idxOf] at h
  exact h.symm

lemma boundaryIndex_inj (xs : List D) (ys : List S) (hny : ys.Nodup)
    (hlen : xs.length = ys.length) {x y : D} (hx : x ∈ xs) (hy : y ∈ xs)
    (he : boundaryIndex xs ys hlen x hx = boundaryIndex xs ys hlen y hy) : x = y := by
  have hi := hny.getElem_inj_iff.mp he
  have hx' := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hx)
  have hy' := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hy)
  have ht : xs[xs.idxOf x]'(List.idxOf_lt_length_iff.mpr hx) =
      xs[xs.idxOf y]'(List.idxOf_lt_length_iff.mpr hy) := by simp only [hi]
  exact hx'.symm.trans (ht.trans hy')

variable [DecidableEq S]

lemma boundaryIndex_commute {f : Perm D} {t : Perm S} {xs : List D} {ys : List S}
    (hf : IsBoundary f xs) (ht : IsBoundary t ys) (hlen : xs.length = ys.length)
    (x : D) (hx : x ∈ xs) :
    boundaryIndex xs ys hlen (f x) (hf.invariant hx) = t (boundaryIndex xs ys hlen x hx) := by
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hx
  have hn : 0 < xs.length := (Nat.zero_le i).trans_lt hi
  have hn' : 0 < ys.length := by omega
  rw [boundaryIndex_get xs ys hf.nodup hlen i hi,ht.turn _ (List.getElem_mem (by omega)),
    List.formPerm_apply_getElem ys ht.nodup i (by omega)]
  have he : f xs[i] = xs[(i+1)%xs.length]'(Nat.mod_lt _ hn) :=
    (hf.turn _ (List.getElem_mem hi)).trans (List.formPerm_apply_getElem xs hf.nodup i hi)
  simp only [he,boundaryIndex_get xs ys hf.nodup hlen,hlen]

/-- Build a coherent index map by selecting one boundary match PER FACE,
not independently per side. This is the coherence step between
word van Kampen diagrams and actual cellular pictures. -/
theorem indexedFaceMap_exists (f : Perm D) (t : Perm S) (label : D → L) (edge : S → L)
    (h : ∀ x : D, ∃ xs : List D, ∃ ys : List S,
      IsBoundary f xs ∧ x ∈ xs ∧ IsBoundary t ys ∧ xs.map label = ys.map edge) :
    ∃ j : D → S, IndexedFaceMap f t j ∧ ∀ x, edge (j x) = label x := by
  let F := Quotient (SameCycle.setoid f)
  let cls : D → F := Quotient.mk _
  let xs : F → List D := fun c => (h c.out).choose
  let ys : F → List S := fun c => (h c.out).choose_spec.choose
  have hd : ∀ c : F, IsBoundary f (xs c) ∧ c.out ∈ xs c ∧
      IsBoundary t (ys c) ∧ (xs c).map label = (ys c).map edge :=
    fun c => (h c.out).choose_spec.choose_spec
  have hlen : ∀ c, (xs c).length = (ys c).length := fun c => by
    have hh := congrArg List.length (hd c).2.2.2
    simpa only [List.length_map] using hh
  have hm : ∀ x, x ∈ xs (cls x) := by
    intro x
    exact (hd (cls x)).1.mem_of_sameCycle (hd (cls x)).2.1
      (Quotient.exact (Quotient.out_eq' (cls x)))
  have hc : ∀ x, cls (f x) = cls x := fun x =>
    Quotient.sound (SameCycle.rfl.apply_right.symm)
  let j : D → S := fun x => boundaryIndex (xs (cls x)) (ys (cls x)) (hlen _) x (hm x)
  refine ⟨j,⟨?_,?_⟩,?_⟩
  · intro x
    dsimp only [j]
    simp only [hc x]
    exact boundaryIndex_commute (hd (cls x)).1 (hd (cls x)).2.2.1 (hlen _) x (hm x)
  · intro x y hxy he
    have hec : cls x = cls y := Quotient.sound hxy
    dsimp only [j] at he
    simp only [← hec] at he
    exact boundaryIndex_inj _ _ (hd (cls x)).2.2.1.nodup (hlen _) (hm x) (hec ▸ hm y) he
  · intro x
    exact boundaryIndex_label _ _ (hlen _) label edge (hd (cls x)).2.2.2 x (hm x)

end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
