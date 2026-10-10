import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import OAI.Computability.BinPacking.Packing.PackingCoordinates

namespace OAI

noncomputable section

namespace BinPackingGap

def excludedPositions {T Pos : Type*} [Fintype Pos]
    (selected : Finset T) (I : T → Pos → Prop) : Finset Pos := by
  classical
  exact Finset.univ.filter fun r => ∃ t ∈ selected, I t r

@[simp] theorem mem_excludedPositions {T Pos : Type*} [Fintype Pos]
    (selected : Finset T) (I : T → Pos → Prop) {r : Pos} :
    r ∈ excludedPositions selected I ↔ ∃ t ∈ selected, I t r := by
  classical
  simp [excludedPositions]

theorem excludedPositions_card_le {T Pos : Type*} [Fintype Pos]
    (selected : Finset T) (I : T → Pos → Prop)
    (hunique : ∀ t ∈ selected, ∀ r s, I t r → I t s → r = s) :
    (excludedPositions selected I).card ≤ selected.card := by
  classical
  have witness (r : ↥(excludedPositions selected I)) : ∃ t ∈ selected, I t r :=
    (mem_excludedPositions selected I).mp r.property
  let f : ↥(excludedPositions selected I) → ↥selected := fun r =>
    ⟨(witness r).choose, (witness r).choose_spec.1⟩
  have hf (r : ↥(excludedPositions selected I)) : I (f r) r :=
    (witness r).choose_spec.2
  have hinj : Function.Injective f := by
    intro r s hrs
    have ht : (f r : T) = (f s : T) := congrArg (fun t : ↥selected => (t : T)) hrs
    apply Subtype.ext
    apply hunique (f r) (f r).property r s (hf r)
    rw [ht]
    exact hf s
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

def excludedRepetitions {E : Type*} {R : ℕ}
    (bad : Finset (E × Fin R)) (e : E) : Finset (Fin R) := by
  classical
  exact Finset.univ.filter fun j => (e, j) ∈ bad

def nonexcludedRepetitions {E : Type*} {R : ℕ}
    (bad : Finset (E × Fin R)) (e : E) : Finset (Fin R) := by
  classical
  exact Finset.univ.filter fun j => (e, j) ∉ bad

@[simp] theorem mem_excludedRepetitions {E : Type*} {R : ℕ}
    (bad : Finset (E × Fin R)) (e : E) {j : Fin R} :
    j ∈ excludedRepetitions bad e ↔ (e, j) ∈ bad := by
  classical
  simp [excludedRepetitions]

@[simp] theorem mem_nonexcludedRepetitions {E : Type*} {R : ℕ}
    (bad : Finset (E × Fin R)) (e : E) {j : Fin R} :
    j ∈ nonexcludedRepetitions bad e ↔ (e, j) ∉ bad := by
  classical
  simp [nonexcludedRepetitions]

theorem excludedRepetitions_card_le {E : Type*} {R : ℕ}
    (bad : Finset (E × Fin R)) (e : E) :
    (excludedRepetitions bad e).card ≤ bad.card := by
  classical
  let f : ↥(excludedRepetitions bad e) → ↥bad := fun j =>
    ⟨(e, j), (mem_excludedRepetitions bad e).mp j.property⟩
  have hinj : Function.Injective f := by
    intro j k hjk
    apply Subtype.ext
    exact congrArg Prod.snd (congrArg (fun x : ↥bad => (x : E × Fin R)) hjk)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

theorem excluded_nonexcluded_card {E : Type*} {R : ℕ}
    (bad : Finset (E × Fin R)) (e : E) :
    (excludedRepetitions bad e).card + (nonexcludedRepetitions bad e).card = R := by
  classical
  have hdis : Disjoint (excludedRepetitions bad e) (nonexcludedRepetitions bad e) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    exact ((mem_nonexcludedRepetitions bad e).mp hk)
      ((mem_excludedRepetitions bad e).mp hj)
  have hunion : excludedRepetitions bad e ∪ nonexcludedRepetitions bad e = Finset.univ := by
    ext j
    by_cases hj : (e, j) ∈ bad <;> simp [hj]
  calc
    _ = (excludedRepetitions bad e ∪ nonexcludedRepetitions bad e).card :=
      (Finset.card_union_of_disjoint hdis).symm
    _ = R := by rw [hunion]; simp

theorem nonexcludedRepetitions_add_card_bound {E : Type*} {R P : ℕ}
    (bad : Finset (E × Fin R)) (e : E) (hbad : bad.card ≤ P) :
    R ≤ P + (nonexcludedRepetitions bad e).card := by
  calc
    R = (excludedRepetitions bad e).card + (nonexcludedRepetitions bad e).card :=
      (excluded_nonexcluded_card bad e).symm
    _ ≤ P + (nonexcludedRepetitions bad e).card :=
      Nat.add_le_add_right ((excludedRepetitions_card_le bad e).trans hbad) _

theorem nonexcludedRepetitions_card_ge {E : Type*} {R P : ℕ}
    (bad : Finset (E × Fin R)) (e : E) (hbad : bad.card ≤ P) :
    R - P ≤ (nonexcludedRepetitions bad e).card := by
  apply Nat.sub_le_iff_le_add.mpr
  simpa only [Nat.add_comm] using nonexcludedRepetitions_add_card_bound bad e hbad

theorem nonexcludedRepetitions_card_ge_real {E : Type*} {R P : ℕ}
    (bad : Finset (E × Fin R)) (e : E) (hbad : bad.card ≤ P) :
    (R : ℝ) - P ≤ ((nonexcludedRepetitions bad e).card : ℝ) := by
  have h : (R : ℝ) ≤ (P : ℝ) + ((nonexcludedRepetitions bad e).card : ℝ) := by
    exact_mod_cast nonexcludedRepetitions_add_card_bound bad e hbad
  apply sub_le_iff_le_add.mpr
  simpa only [add_comm] using h

theorem nonexcludedRepetitions_card_ge_of_unique_hits {T E : Type*} [Fintype E]
    {R P : ℕ} (selected : Finset T) (I : T → E × Fin R → Prop)
    (hunique : ∀ t ∈ selected, ∀ r s, I t r → I t s → r = s)
    (hselected : selected.card ≤ P) (e : E) :
    R - P ≤ (nonexcludedRepetitions (excludedPositions selected I) e).card :=
  nonexcludedRepetitions_card_ge _ e ((excludedPositions_card_le selected I hunique).trans hselected)

theorem nonexcludedRepetitions_card_ge_real_of_unique_hits {T E : Type*} [Fintype E]
    {R P : ℕ} (selected : Finset T) (I : T → E × Fin R → Prop)
    (hunique : ∀ t ∈ selected, ∀ r s, I t r → I t s → r = s)
    (hselected : selected.card ≤ P) (e : E) :
    (R : ℝ) - P ≤ ((nonexcludedRepetitions (excludedPositions selected I) e).card : ℝ) :=
  nonexcludedRepetitions_card_ge_real _ e
    ((excludedPositions_card_le selected I hunique).trans hselected)

namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

def tupleHitsJob (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (r : D.Position) : Prop :=
  (tupleClosedInterval p e t ∩
    Geometry.closedJobCell D.graph.edges.length D.R D.geometryBound D.L r).Nonempty

def excludedAt (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex) :
    Finset D.Position :=
  excludedPositions (zeroPositiveTuples p e v) (tupleHitsJob p e)

theorem selected_hits_job_unique (p : Packing I b) (e : D.Item ≃ I.Item)
    (hL : 1 ≤ D.L) (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ zeroPositiveTuples p e v) {r s : D.Position}
    (hr : tupleHitsJob p e t r) (hs : tupleHitsJob p e t s) : r = s :=
  Geometry.closedJobCell_unique_of_short_interval hL
    (selected_interval_length_first p e v t ht) hr hs

theorem excludedAt_card_le (p : Packing I b) (e : D.Item ≃ I.Item)
    (hL : 1 ≤ D.L) (v : D.Vertex) : (excludedAt p e v).card ≤ D.P := by
  apply (excludedPositions_card_le (zeroPositiveTuples p e v) (tupleHitsJob p e) ?_).trans
    (zeroPositiveTuples_card_le p e v)
  intro t ht r s hr hs
  exact selected_hits_job_unique p e hL v t ht hr hs

def goodRepetitions (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (edge : D.Edge) : Finset (Fin D.R) :=
  nonexcludedRepetitions (excludedAt p e v) edge

theorem goodRepetitions_card_ge (p : Packing I b) (e : D.Item ≃ I.Item)
    (hL : 1 ≤ D.L) (v : D.Vertex) (edge : D.Edge) :
    D.R - D.P ≤ (goodRepetitions p e v edge).card :=
  nonexcludedRepetitions_card_ge _ edge (excludedAt_card_le p e hL v)

theorem goodRepetitions_card_ge_real (p : Packing I b) (e : D.Item ≃ I.Item)
    (hL : 1 ≤ D.L) (v : D.Vertex) (edge : D.Edge) :
    (D.R : ℝ) - D.P ≤ ((goodRepetitions p e v edge).card : ℝ) :=
  nonexcludedRepetitions_card_ge_real _ edge (excludedAt_card_le p e hL v)

theorem covering_not_selected_of_nonexcluded (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (r : D.Position) (hr : r ∉ excludedAt p e v)
    (t : p.TableBin (subclass e))
    (ht : t ∈ tupleCovering p e v
      (Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L r)) :
    t ∉ zeroPositiveTuples p e v := by
  intro hselected
  apply hr
  apply (mem_excludedPositions _ _).mpr
  refine ⟨t, hselected, ?_⟩
  obtain ⟨_, hlo, hhi⟩ := (mem_tupleCovering p e v _ t).mp ht
  refine ⟨Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L r,
    ⟨hlo, hhi.le⟩, ?_⟩
  exact Geometry.jobInterior_mem_closedJobCell _ _ _ _ _

end PackingCounts
end BinPackingGap

end

end OAI
