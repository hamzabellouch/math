import OAI.Combinatorics.LowSpaceSubsetSum.Storage.BackgroundDomains

namespace OAI

/-! # Consecutive background blocks from a stored sorted domain

Eight prefix-sum offsets determine the physical array reads. The finite
background-color equivalence is used only to prove that these rows are the
same blocks as in the finite-partition specification.
-/

namespace LowSpaceSubsetSum.StoredBackgroundBlocks

open scoped BigOperators
variable {n m : ℕ}

def index (counts : Vector ℕ 8) (hc : (∑ i : Fin 8, counts[i.val]) = m)
    (i : Fin 8) (k : Fin counts[i.val]) : Fin m :=
  ⟨(finSigmaFinEquiv (n := fun j : Fin 8 => counts[j.val]) ⟨i, k⟩).val,
    by simpa only [hc] using
      (finSigmaFinEquiv (n := fun j : Fin 8 => counts[j.val]) ⟨i, k⟩).isLt⟩

theorem index_value (counts : Vector ℕ 8) (hc : (∑ i : Fin 8, counts[i.val]) = m)
    (i : Fin 8) (k : Fin counts[i.val]) :
    (index counts hc i k).val =
      (∑ j : Fin i.val, counts[(Fin.castLE i.isLt.le j).val]) + k.val :=
  finSigmaFinEquiv_apply (n := fun j : Fin 8 => counts[j.val]) ⟨i, k⟩

def row (xs : Vector (Fin n) m) (counts : Vector ℕ 8)
    (hc : (∑ i : Fin 8, counts[i.val]) = m) (i : Fin 8) : List (Fin n) :=
  List.ofFn (fun k : Fin counts[i.val] => xs[(index counts hc i k).val])

theorem row_length (xs : Vector (Fin n) m) (counts : Vector ℕ 8)
    (hc : (∑ i : Fin 8, counts[i.val]) = m) (i : Fin 8) :
    (row xs counts hc i).length = counts[i.val] := List.length_ofFn

theorem point_source (V : Finset (Fin n)) (xs : Vector (Fin n) V.card)
    (hx : ∀ k : Fin V.card, xs[k.val] = ((V.orderIsoOfFin rfl) k).val)
    (counts : Vector ℕ 8) (hc : (∑ i : Fin 8, counts[i.val]) = V.card)
    (i : Fin 8) (k : Fin counts[i.val]) :
    xs[(index counts hc i k).val] =
      ((backgroundIndexEquiv V (fun j => counts[j.val]) hc).symm ⟨i, k⟩).val := by
  rw [hx]
  rfl

theorem row_source (V : Finset (Fin n)) (xs : Vector (Fin n) V.card)
    (hx : ∀ k : Fin V.card, xs[k.val] = ((V.orderIsoOfFin rfl) k).val)
    (counts : Vector ℕ 8) (hc : (∑ i : Fin 8, counts[i.val]) = V.card) (i : Fin 8) :
    (row xs counts hc i).toFinset =
      V.filter (fun x => backgroundColor V (fun j => counts[j.val]) hc x = i) := by
  classical
  let e := backgroundIndexEquiv V (fun j => counts[j.val]) hc
  ext x
  simp only [row, List.mem_toFinset, List.mem_ofFn, Finset.mem_filter]
  constructor
  · rintro ⟨k, hk⟩
    have he : (e.symm ⟨i, k⟩).val = x := (point_source V xs hx counts hc i k).symm.trans hk
    have hm : x ∈ V := he ▸ (e.symm ⟨i, k⟩).property
    refine ⟨hm, ?_⟩
    have hv : (⟨x, hm⟩ : ↥V) = e.symm ⟨i, k⟩ := Subtype.ext he.symm
    simp only [backgroundColor, dite_eq_left hm, hv]
    exact congrArg Sigma.fst (e.apply_symm_apply ⟨i, k⟩)
  · rintro ⟨hm, hi⟩
    let v : ↥V := ⟨x, hm⟩
    have hi' : (e v).1 = i := by
      simpa only [backgroundColor, dite_eq_left hm] using hi
    rcases he : e v with ⟨j, k⟩
    have hj : j = i := by simpa only [he] using hi'
    subst j
    refine ⟨k, ?_⟩
    rw [point_source V xs hx counts hc i k]
    change (e.symm ⟨i, k⟩).val = x
    rw [← he, e.symm_apply_apply]

theorem row_source_of_size (V : Finset (Fin n)) (hm : V.card = m)
    (xs : Vector (Fin n) m)
    (hx : ∀ k : Fin m, xs[k.val] = ((V.orderIsoOfFin hm) k).val)
    (counts : Vector ℕ 8) (hc : (∑ i : Fin 8, counts[i.val]) = m) (i : Fin 8) :
    (row xs counts hc i).toFinset =
      V.filter (fun x => backgroundColor V (fun j => counts[j.val]) (hc.trans hm.symm) x = i) := by
  subst m
  exact row_source V xs hx counts hc i

def run (xs : Vector (Fin n) m) (counts : Vector ℕ 8)
    (hc : (∑ i : Fin 8, counts[i.val]) = m) : Vector (List (Fin n)) 8 × ℕ :=
  (Vector.ofFn (row xs counts hc), 32 * m + 200)

theorem run_work (xs : Vector (Fin n) m) (counts : Vector ℕ 8)
    (hc : (∑ i : Fin 8, counts[i.val]) = m) : (run xs counts hc).2 = 32 * m + 200 := rfl

end LowSpaceSubsetSum.StoredBackgroundBlocks

end OAI
