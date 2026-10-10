import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import OAI.Computability.BinPacking.Packing.K4Graph
import OAI.Computability.BinPacking.Reductions.Target

namespace OAI

namespace BinPackingGap.LiteralSlotGraph

open BinPackingGames.Foundations.Target

def vertexCount (F : Formula) : ℕ := 3 * F.clauses.length

abbrev Vertex (F : Formula) := Fin (vertexCount F)

def occurrence (F : Formula) (u : Vertex F) : Fin F.clauses.length :=
  ⟨u.val / 3, by have := u.isLt; unfold vertexCount at this; omega⟩

def slot (F : Formula) (u : Vertex F) : Fin 3 :=
  ⟨u.val % 3, Nat.mod_lt _ (by decide)⟩

def index (F : Formula) (c : Fin F.clauses.length) (j : Fin 3) : Vertex F :=
  ⟨3 * c.val + j.val, by
    have := c.isLt
    have := j.isLt
    unfold vertexCount
    omega⟩

@[simp] theorem occurrence_index (F : Formula) (c : Fin F.clauses.length) (j : Fin 3) :
    occurrence F (index F c j) = c := by
  apply Fin.ext
  dsimp [occurrence, index]
  have := j.isLt
  omega

@[simp] theorem slot_index (F : Formula) (c : Fin F.clauses.length) (j : Fin 3) :
    slot F (index F c j) = j := by
  apply Fin.ext
  dsimp [slot, index]
  have := j.isLt
  omega

@[simp] theorem index_occurrence_slot (F : Formula) (u : Vertex F) :
    index F (occurrence F u) (slot F u) = u := by
  apply Fin.ext
  dsimp [index, occurrence, slot]
  omega

def literal (F : Formula) (u : Vertex F) : Literal F.variables :=
  (F.clauses[occurrence F u])[slot F u]

@[simp] theorem literal_index (F : Formula) (c : Fin F.clauses.length) (j : Fin 3) :
    literal F (index F c j) = (F.clauses[c])[j] := by
  simp [literal]

def Conflict (F : Formula) (u v : Vertex F) : Prop :=
  occurrence F u = occurrence F v ∨
    ((literal F u).variableIndex = (literal F v).variableIndex ∧
      (literal F u).positive ≠ (literal F v).positive)

instance (F : Formula) (u v : Vertex F) : Decidable (Conflict F u v) := by
  unfold Conflict
  infer_instance

theorem conflict_symm (F : Formula) {u v : Vertex F} (h : Conflict F u v) :
    Conflict F v u := by
  rcases h with h | ⟨hvar, hsign⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨hvar.symm, Ne.symm hsign⟩

def edgeList (F : Formula) : List (Vertex F × Vertex F) :=
  ((List.finRange (vertexCount F)).product (List.finRange (vertexCount F))).filter
    (fun e => decide (e.1 < e.2 ∧ Conflict F e.1 e.2))

@[simp] theorem mem_edgeList (F : Formula) (u v : Vertex F) :
    (u, v) ∈ edgeList F ↔ u < v ∧ Conflict F u v := by
  simp [edgeList]

def graph (F : Formula) : GraphInput where
  n := vertexCount F
  edges := edgeList F
  ordered := by
    intro e he
    exact ((mem_edgeList F e.1 e.2).mp he).1
  distinct :=
    ((List.nodup_finRange (vertexCount F)).product
      (List.nodup_finRange (vertexCount F))).filter _

@[simp] theorem graph_n (F : Formula) : (graph F).n = 3 * F.clauses.length := rfl

theorem graph_edges_nonempty (F : Formula) (hF : F.clauses ≠ []) :
    (graph F).edges ≠ [] := by
  have hm : 0 < F.clauses.length := List.length_pos_iff.mpr hF
  let c : Fin F.clauses.length := ⟨0, hm⟩
  have he : (index F c 0, index F c 1) ∈ edgeList F := by
    apply (mem_edgeList _ _ _).mpr
    constructor
    · change 3 * c.val + 0 < 3 * c.val + 1
      omega
    · exact Or.inl (by simp)
  intro hn
  change edgeList F = [] at hn
  simp [hn] at he

def Independent (F : Formula) (S : Finset (Vertex F)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬Conflict F u v

theorem independent_complement_of_cover (F : Formula) (C : Finset (Vertex F))
    (hC : (graph F).IsCover C) : Independent F (Finset.univ \ C) := by
  intro u hu v hv hne hconf
  have huC := (Finset.mem_sdiff.mp hu).2
  have hvC := (Finset.mem_sdiff.mp hv).2
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have he := (mem_edgeList F u v).mpr ⟨hlt, hconf⟩
    rcases hC (u, v) he with h | h
    · exact huC h
    · exact hvC h
  · have he := (mem_edgeList F v u).mpr ⟨hgt, conflict_symm F hconf⟩
    rcases hC (v, u) he with h | h
    · exact hvC h
    · exact huC h

theorem cover_complement_of_independent (F : Formula) (S : Finset (Vertex F))
    (hS : Independent F S) : (graph F).IsCover (Finset.univ \ S) := by
  classical
  intro e he
  have hed := (mem_edgeList F e.1 e.2).mp he
  by_cases hleft : e.1 ∈ S
  · right
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hright
    exact hS e.1 hleft e.2 hright (ne_of_lt hed.1) hed.2
  · left
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hleft⟩

theorem occurrence_injective_on_independent (F : Formula) (S : Finset (Vertex F))
    (hS : Independent F S) : Set.InjOn (occurrence F) S := by
  intro u hu v hv hsame
  by_contra hne
  exact hS u hu v hv hne (Or.inl hsame)

theorem literal_true_iff {n : ℕ} (l : Literal n) (A : Fin n → Bool) :
    l.eval A = true ↔ A l.variableIndex = l.positive := by
  cases hs : l.positive <;> cases ha : A l.variableIndex <;>
    simp [Literal.eval, hs, ha]

theorem true_literals_not_complementary (F : Formula) (A : Fin F.variables → Bool)
    {u v : Vertex F} (hu : (literal F u).eval A = true)
    (hv : (literal F v).eval A = true)
    (hvar : (literal F u).variableIndex = (literal F v).variableIndex) :
    (literal F u).positive = (literal F v).positive := by
  have hau := (literal_true_iff _ _).mp hu
  have hav := (literal_true_iff _ _).mp hv
  exact hau.symm.trans ((congrArg A hvar).trans hav)

theorem assignment_of_independent (F : Formula) (S : Finset (Vertex F))
    (hS : Independent F S) :
    ∃ A : Fin F.variables → Bool, ∀ u ∈ S, (literal F u).eval A = true := by
  classical
  let A : Fin F.variables → Bool := fun x =>
    decide (∃ v ∈ S, (literal F v).variableIndex = x ∧ (literal F v).positive = true)
  refine ⟨A, ?_⟩
  intro u hu
  apply (literal_true_iff _ _).mpr
  cases hs : (literal F u).positive with
  | true =>
      have hex : ∃ v ∈ S, (literal F v).variableIndex = (literal F u).variableIndex ∧
          (literal F v).positive = true := ⟨u, hu, rfl, hs⟩
      simp [A, hex]
  | false =>
      have hn : ¬ ∃ v ∈ S,
          (literal F v).variableIndex = (literal F u).variableIndex ∧
          (literal F v).positive = true := by
        rintro ⟨v, hv, hvar, hsign⟩
        have hne : u ≠ v := by
          intro heq
          subst v
          simp [hs] at hsign
        exact hS u hu v hv hne (Or.inr ⟨hvar.symm, by simp [hs, hsign]⟩)
      simp [A, hn]

def chosenSlot (F : Formula) (A : Fin F.variables → Bool)
    (c : Fin F.clauses.length) : Fin 3 :=
  if (F.clauses[c])[0].eval A = true then 0
  else if (F.clauses[c])[1].eval A = true then 1 else 2

theorem chosenSlot_true (F : Formula) (A : Fin F.variables → Bool)
    (c : Fin F.clauses.length) (hc : (F.clauses[c]).eval A = true) :
    (F.clauses[c])[chosenSlot F A c].eval A = true := by
  unfold chosenSlot
  split_ifs with h0 h1
  · exact h0
  · exact h1
  · simp only [Clause.eval, Bool.or_eq_true] at hc
    rcases hc with (hc | hc) | hc
    · exact False.elim (h0 hc)
    · exact False.elim (h1 hc)
    · exact hc

def selectedSlots (F : Formula) (A : Fin F.variables → Bool) : Finset (Vertex F) :=
  Finset.univ.image (fun c => index F c (chosenSlot F A c))

theorem selectedSlots_card (F : Formula) (A : Fin F.variables → Bool) :
    (selectedSlots F A).card = F.clauses.length := by
  have hinj : Function.Injective (fun c => index F c (chosenSlot F A c)) := by
    intro c d h
    have h' := congrArg (occurrence F) h
    simpa using h'
  simpa [selectedSlots] using
    Finset.card_image_of_injective (Finset.univ : Finset (Fin F.clauses.length)) hinj

theorem selectedSlots_independent (F : Formula) (A : Fin F.variables → Bool)
    (hA : ∀ c ∈ F.clauses, c.eval A = true) : Independent F (selectedSlots F A) := by
  intro u hu v hv hne hconf
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hv
  rcases hconf with hsame | ⟨hvar, hsign⟩
  · have hcd : c = d := by simpa using hsame
    subst d
    exact hne rfl
  · apply hsign
    apply true_literals_not_complementary F A
    · simpa using chosenSlot_true F A c (hA _ (List.getElem_mem c.isLt))
    · simpa using chosenSlot_true F A d (hA _ (List.getElem_mem d.isLt))
    · exact hvar

theorem coverAtMost_of_satisfiable (F : Formula) (hF : F.Satisfiable) :
    (graph F).CoverAtMost (2 * F.clauses.length) := by
  classical
  obtain ⟨A, hA⟩ := hF
  refine ⟨Finset.univ \ selectedSlots F A,
    cover_complement_of_independent F _ (selectedSlots_independent F A hA), ?_⟩
  change ((Finset.univ : Finset (Vertex F)) \ selectedSlots F A).card ≤
    2 * F.clauses.length
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin, selectedSlots_card]
  unfold vertexCount
  omega

end BinPackingGap.LiteralSlotGraph

end OAI
