import OAI.Combinatorics.VariableWL.Subdivision

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11

namespace VariableWL.Wrapping
open scoped CharTwo
open Markers
abbrev Bit := ZMod 2

variable {I : Type uVariable1} {V : Type uVariable2} [DecidableEq I] {G : SimpleGraph V}

structure RowDiagram (G : SimpleGraph V) (next : Equiv.Perm I) where
  boundary : V → I
  horizontal : V → V → Option I
  symmetric : ∀ u v, G.Adj u v → horizontal u v = horizontal v u
  shape : ∀ u v, G.Adj u v →
    match horizontal u v with
    | none => boundary u = boundary v
    | some i => (boundary u = i ∧ boundary v = next i) ∨
        (boundary v = i ∧ boundary u = next i)

namespace RowDiagram

variable {next : Equiv.Perm I} (D : RowDiagram G next)

def rowWeight (i : I) (u v : V) : Bit := if D.horizontal u v = some i then 1 else 0

def Wraps (marked : I) : Prop :=
  ∃ v : V, ∃ p : G.Walk v v, walkSum (D.rowWeight marked) p = 1

theorem boundary_incidence (i : I) {u v : V} (h : G.Adj u v) :
    (if D.boundary u = i then (1 : Bit) else 0) +
      (if D.boundary v = i then 1 else 0) =
    D.rowWeight i u v + D.rowWeight (next.symm i) u v := by
  have hs := D.shape u v h
  cases hh : D.horizontal u v with
  | none =>
    simp only [hh] at hs
    simp [rowWeight, hh, hs]
  | some j =>
    simp only [hh] at hs
    rcases hs with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · simp [rowWeight, hh, hu, hv, ← next.eq_symm_apply]
    · simp [rowWeight, hh, hu, hv, ← next.eq_symm_apply, add_comm]

theorem row_parity_next {v : V} (p : G.Walk v v) (i : I) :
    walkSum (D.rowWeight (next i)) p = walkSum (D.rowWeight i) p := by
  classical
  let s (v : V) : Bit := if D.boundary v = next i then 1 else 0
  have ht := walkSum_of_potential
    (fun u v => D.rowWeight (next i) u v + D.rowWeight i u v) s
    (fun u v h => by simpa [s] using D.boundary_incidence (next i) h) p
  rw [walkSum_add] at ht
  have hh := congrArg (fun x => x + walkSum (D.rowWeight i) p) ht
  simpa [add_assoc] using hh

theorem row_parity_all
    (horbit : ∀ i j : I, ∃ m : ℕ, next^[m] i = j)
    {v : V} (p : G.Walk v v) (i j : I) :
    walkSum (D.rowWeight i) p = walkSum (D.rowWeight j) p := by
  obtain ⟨m, rfl⟩ := horbit i j
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', D.row_parity_next]
    exact ih

theorem finRotate_orbit {r : ℕ} [NeZero r] (i j : Fin r) :
    ∃ m : ℕ, (finRotate r)^[m] i = j := by
  refine ⟨(j-i).val, ?_⟩
  rw [← finCycle_eq_finRotate_iterate]
  simp

theorem covers_rows {B : Type uVariable3} [DecidableEq B] (U : Finset B) (row : B → I)
    (hcover : ∀ u v, G.Adj u v → ∀ i, D.horizontal u v = some i → i ∈ U.image row)
    (horbit : ∀ i j : I, ∃ m : ℕ, next^[m] i = j)
    {marked : I} (hw : D.Wraps marked) : ∀ i, i ∈ U.image row := by
  classical
  obtain ⟨v, p, hp⟩ := hw
  intro i
  by_contra hi
  have hz : walkSum (D.rowWeight i) p = 0 := by
    rw [walkSum_congr (ω' := fun _ _ => 0) (fun u v h => ?_), walkSum_zero]
    simp only [rowWeight, ite_eq_right_iff, one_ne_zero, imp_false]
    exact fun hh => hi (hcover u v h i hh)
  have he := D.row_parity_all horbit p i marked
  rw [hz, hp] at he
  exact zero_ne_one he

theorem blocks_card_ge [Fintype I] {B : Type uVariable4} [DecidableEq B]
    (U : Finset B) (row : B → I)
    (hcover : ∀ u v, G.Adj u v → ∀ i, D.horizontal u v = some i → i ∈ U.image row)
    (horbit : ∀ i j : I, ∃ m : ℕ, next^[m] i = j)
    {marked : I} (hw : D.Wraps marked) : Fintype.card I ≤ U.card := by
  have he : U.image row = Finset.univ := Finset.eq_univ_of_forall
    (D.covers_rows U row hcover horbit hw)
  calc
    Fintype.card I = (U.image row).card := by rw [he, Finset.card_univ]
    _ ≤ U.card := Finset.card_image_le

theorem row_injective [Fintype I] {B : Type uVariable5} [DecidableEq B]
    (U : Finset B) (row : B → I)
    (hcover : ∀ u v, G.Adj u v → ∀ i, D.horizontal u v = some i → i ∈ U.image row)
    (horbit : ∀ i j : I, ∃ m : ℕ, next^[m] i = j)
    {marked : I} (hw : D.Wraps marked) (hc : U.card = Fintype.card I) :
    Set.InjOn row (↑U : Set B) := by
  apply Finset.card_image_iff.mp
  have he : U.image row = Finset.univ := Finset.eq_univ_of_forall
    (D.covers_rows U row hcover horbit hw)
  rw [he, Finset.card_univ, hc]

end RowDiagram

end VariableWL.Wrapping

namespace VariableWL.Wrapping.RowDiagram
open scoped CharTwo
open Markers
variable {I : Type uVariable6} {V : Type uVariable7} {L : Type uVariable8} [DecidableEq I] [DecidableEq L]
    {G : SimpleGraph V} {next : Equiv.Perm I} (D : RowDiagram G next)

def Labeled (label : V → L) (first last : I → L) : Prop :=
  ∀ u v, G.Adj u v →
    match D.horizontal u v with
    | none => (D.boundary u, label u) = (D.boundary v, label v)
    | some i =>
      ((D.boundary u, label u) = (i, first i) ∧
        (D.boundary v, label v) = (next i, last i)) ∨
      ((D.boundary v, label v) = (i, first i) ∧
        (D.boundary u, label u) = (next i, last i))

theorem label_incidence (label : V → L) (first last : I → L)
    (hl : D.Labeled label first last) (i : I) (x : L) {u v : V} (h : G.Adj u v) :
    (if (D.boundary u, label u) = (i,x) then (1 : Bit) else 0) +
      (if (D.boundary v, label v) = (i,x) then 1 else 0) =
    D.rowWeight i u v * (if first i = x then 1 else 0) +
      D.rowWeight (next.symm i) u v * (if last (next.symm i) = x then 1 else 0) := by
  have hs := hl u v h
  cases hh : D.horizontal u v with
  | none =>
    simp only [hh] at hs
    rw [hs]
    simp [rowWeight, hh]
  | some j =>
    simp only [hh] at hs
    rcases hs with ⟨hu, hv⟩ | ⟨hv, hu⟩
    all_goals
      rw [hu, hv]
      by_cases hji : j = i <;> by_cases hjp : j = next.symm i <;>
        simp_all [rowWeight, ← next.eq_symm_apply, add_comm]

theorem label_coherence (label : V → L) (first last : I → L)
    (hl : D.Labeled label first last)
    (horbit : ∀ i j : I, ∃ m : ℕ, next^[m] i = j)
    {marked : I} (hw : D.Wraps marked) : ∀ i, last i = first (next i) := by
  obtain ⟨v, p, hp⟩ := hw
  have hpar (i : I) : walkSum (D.rowWeight i) p = 1 :=
    (D.row_parity_all horbit p i marked).trans hp
  have hc (i : I) : last (next.symm i) = first i := by
    let s (v : V) : Bit := if (D.boundary v, label v) = (i,first i) then 1 else 0
    have ht := walkSum_of_potential
      (fun u v => D.rowWeight i u v * (if first i = first i then 1 else 0) +
        D.rowWeight (next.symm i) u v * (if last (next.symm i) = first i then 1 else 0)) s
      (fun u v h => D.label_incidence label first last hl i (first i) h) p
    rw [walkSum_add, walkSum_mul, walkSum_mul, hpar, hpar] at ht
    by_contra he
    simp [he] at ht
  intro i
  simpa using hc (next i)

end VariableWL.Wrapping.RowDiagram

namespace VariableWL.Wrapping
variable {I : Type uVariable9} {B : Type uVariable10} {L : Type uVariable11} [Fintype I] [DecidableEq I] [DecidableEq B]

theorem overlap_compl_card_le_one (U A B' : Finset B) (row : B → I)
    (hA : A ⊆ U) (hB : B' ⊆ U) (hU : U.card ≤ Fintype.card I + 1)
    (hcA : A.card = Fintype.card I) (hcB : B'.card = Fintype.card I)
    (hi : Set.InjOn row (↑A : Set B)) :
    ((A ∩ B').image row)ᶜ.card ≤ 1 := by
  have hsub : A ∪ B' ⊆ U := Finset.union_subset hA hB
  have hle := Finset.card_le_card hsub
  have hcard := Finset.card_union_add_card_inter A B'
  have hinj : Set.InjOn row (↑(A ∩ B') : Set B) := hi.mono (by
    intro x hx; exact (Finset.mem_inter.mp hx).1)
  rw [Finset.card_compl, Finset.card_image_iff.mpr hinj]
  omega

theorem adjacent_cover (next : Equiv.Perm I) (hnofix : ∀ i, next i ≠ i)
    (S : Finset I) (hS : Sᶜ.card ≤ 1) (i : I) : i ∈ S ∨ next.symm i ∈ S := by
  by_contra h
  push Not at h
  have hi : next.symm i ≠ i := by
    intro he
    have hh := congrArg next he
    exact hnofix i (by simpa using hh.symm)
  have hsub : {i, next.symm i} ⊆ Sᶜ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_compl.mpr h.1
    · exact Finset.mem_compl.mpr h.2
  have hc := Finset.card_le_card hsub
  rw [Finset.card_pair hi.symm] at hc
  omega

theorem overlap_address_unique (next : Equiv.Perm I) (hnofix : ∀ i, next i ≠ i)
    (U A B' : Finset B) (row : B → I)
    (hA : A ⊆ U) (hB : B' ⊆ U) (hU : U.card ≤ Fintype.card I + 1)
    (hcA : A.card = Fintype.card I) (hcB : B'.card = Fintype.card I)
    (hi : Set.InjOn row (↑A : Set B)) (a a' : I → L)
    (hlabel : ∀ b ∈ A ∩ B', a (row b) = a' (row b) ∧
      a (next (row b)) = a' (next (row b))) : a = a' := by
  funext i
  have hc := overlap_compl_card_le_one U A B' row hA hB hU hcA hcB hi
  rcases adjacent_cover next hnofix _ hc i with h | h
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h
    exact (hlabel b hb).1
  · obtain ⟨b, hb, hbi⟩ := Finset.mem_image.mp h
    have hh := (hlabel b hb).2
    simpa only [hbi, Equiv.apply_symm_apply] using hh

theorem finRotate_no_fixed {r : ℕ} (hr : 2 ≤ r) (i : Fin r) : finRotate r i ≠ i := by
  have h : i ∈ (finRotate r).support := by
    rw [support_finRotate_of_le hr]
    exact Finset.mem_univ i
  exact Equiv.Perm.mem_support.mp h

end VariableWL.Wrapping

end OAI
