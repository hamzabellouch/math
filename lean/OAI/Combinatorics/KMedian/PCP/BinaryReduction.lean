import Mathlib
import OAI.Combinatorics.KMedian.PCP.AlphabetReduction

namespace OAI

section Inline_PCPBinaryReduction

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

theorem testRate_singleton {S : Type} [Fintype S] [DecidableEq S] (x : S) :
    testRate (fun s => s = x) = 1 / Fintype.card S := by
  classical
  rw [testRate_eq_count]
  have hf : univ.filter (fun s : S => s = x) = {x} := by
    ext s
    simp
  rw [hf]
  simp

theorem testRate_ge_atom {S : Type} [Fintype S] (p : S → Prop) (x : S) (hx : p x) :
    1 / (Fintype.card S : ℝ) ≤ testRate p := by
  classical
  rw [← testRate_singleton x]
  exact testRate_mono (by intro s hs; simpa only [hs] using hx)

namespace IncidenceReduction
variable {P T : Type} [Fintype T] (C : FourCSP P T)
abbrev Label := BitVector (Fin 4)
abbrev Position := P ⊕ T
abbrev Test := T × Fin 4

def reduced : BinaryCSP (Position (P := P) (T := T)) (Test (T := T)) Label where
  left t := .inr t.1
  right t := .inl ((C.query t.1).address t.2)
  allowed t := univ.filter (fun p => (C.query t.1).accept p.1 = true ∧ p.1 t.2 = p.2 0)

omit [Fintype T] in
@[simp] theorem allowed_iff (t : T × Fin 4) (x y : Label) :
    (x,y) ∈ (reduced C).allowed t ↔ (C.query t.1).accept x = true ∧ x t.2 = y 0 := by
  simp [reduced]

def decoded (a : P ⊕ T → Label) : P → Bit := fun p => a (.inl p) 0

omit [Fintype T] in
theorem bad_incidence (a : P ⊕ T → Label) (t : T)
    (ht : (C.query t).Rejects (decoded a)) :
    ∃ j : Fin 4, (a ((reduced C).left (t,j)), a ((reduced C).right (t,j))) ∉
      (reduced C).allowed (t,j) := by
  by_contra h
  push Not at h
  have hall (j : Fin 4) := (allowed_iff C (t,j) _ _).mp (h j)
  have ha : a (.inr t) = decoded a ∘ (C.query t).address := by
    funext j
    exact (hall j).2
  have hy := (hall 0).1
  exact ht (ha ▸ hy)

theorem sound (a : P ⊕ T → Label) :
    C.rejection (decoded a) / 4 ≤ (reduced C).rejection a := by
  classical
  rw [BinaryCSP.rejection, testRate_prod (S := T) (T := Fin 4)
    (fun t j => (a ((reduced C).left (t,j)), a ((reduced C).right (t,j))) ∉
      (reduced C).allowed (t,j))]
  unfold FourCSP.rejection testRate
  rw [Finset.expect_div]
  apply expect_le_expect
  intro t _
  change (@ite ℝ ((C.query t).Rejects (decoded a)) (Classical.propDecidable _) 1 0)/4 ≤
    testRate (fun j : Fin 4 => (a ((reduced C).left (t,j)), a ((reduced C).right (t,j))) ∉
      (reduced C).allowed (t,j))
  by_cases ht : (C.query t).Rejects (decoded a)
  · rw [ite_eq_left ht]
    obtain ⟨j,hj⟩ := bad_incidence C a t ht
    simpa only [Fintype.card_fin, Nat.cast_ofNat] using testRate_ge_atom
      (fun j : Fin 4 => (a ((reduced C).left (t,j)), a ((reduced C).right (t,j))) ∉
        (reduced C).allowed (t,j)) j hj
  · rw [ite_eq_right ht, zero_div]
    exact testRate_nonneg _

omit [Fintype T] in
theorem complete (a : P → Bit) (ha : C.Satisfies a) :
    ∃ b, (reduced C).Satisfies b := by
  refine ⟨Sum.elim (fun p (_ : Fin 4) => a p) (fun t => a ∘ (C.query t).address),?_⟩
  rintro ⟨t,j⟩
  apply (allowed_iff C _ _ _).mpr
  refine ⟨?_,rfl⟩
  exact not_not.mp (ha t)

end IncidenceReduction

namespace AlphabetReduction
variable {V E K : Type} [Fintype V] [Fintype E] [Fintype K] [DecidableEq K]
variable (C : BinaryCSP V E (BitVector K))

instance positionFintype : Fintype (Position C) := inferInstance

def binary := IncidenceReduction.reduced (reduced C)

omit [Fintype V] in
theorem binary_sound (a : Position C ⊕ Test (E := E) (K := K) → IncidenceReduction.Label) :
    C.rejection (decoded C (IncidenceReduction.decoded a)) / 384 ≤ (binary C).rejection a := by
  have h₁ := sound C (IncidenceReduction.decoded a)
  have h₂ := IncidenceReduction.sound (reduced C) a
  change _ ≤ (IncidenceReduction.reduced (reduced C)).rejection a
  linarith

omit [Fintype V] [Fintype E] in
theorem binary_complete (x : V → BitVector K) (hx : C.Satisfies x) :
    ∃ a, (binary C).Satisfies a := by
  obtain ⟨a,ha⟩ := complete C x hx
  exact IncidenceReduction.complete (reduced C) a ha

noncomputable def interiorBound (K : Type) [Fintype K] [DecidableEq K] : ℕ :=
  ∑ R : Relations K, Fintype.card (BitVector (LocalRelation.Vars (R : LocalRelation.Relation K)) ⊕
    BitVector (LocalRelation.Vars (R : LocalRelation.Relation K) ×
      LocalRelation.Vars (R : LocalRelation.Relation K)))

omit [Fintype V] [Fintype E] in
theorem interior_card_le (e : E) : Fintype.card (Interior C e) ≤ interiorBound K := by
  classical
  unfold interiorBound
  exact single_le_sum
    (f := fun R : Relations K => Fintype.card
      (BitVector (LocalRelation.Vars (R : LocalRelation.Relation K)) ⊕
        BitVector (LocalRelation.Vars (R : LocalRelation.Relation K) ×
          LocalRelation.Vars (R : LocalRelation.Relation K))))
    (fun _ _ => Nat.zero_le _) (mem_univ (C.allowed e))

theorem position_card_le : Fintype.card (Position C) ≤
    Fintype.card V * Fintype.card (BitVector K) + Fintype.card E * interiorBound K := by
  classical
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_sigma]
  gcongr
  calc
    ∑ e : E, Fintype.card (Interior C e) ≤ ∑ _e : E, interiorBound K :=
      sum_le_sum (fun e _ => interior_card_le C e)
    _ = _ := by simp

theorem test_card : Fintype.card (Test (E := E) (K := K)) =
    Fintype.card E * Fintype.card (EdgeSample K) := Fintype.card_prod _ _

theorem binary_card_bounds :
    Fintype.card (Position C ⊕ Test (E := E) (K := K)) ≤
      Fintype.card V * Fintype.card (BitVector K) +
        Fintype.card E * (interiorBound K + Fintype.card (EdgeSample K)) ∧
    Fintype.card (Test (E := E) (K := K) × Fin 4) =
      Fintype.card E * (4 * Fintype.card (EdgeSample K)) := by
  constructor
  · rw [Fintype.card_sum, test_card, Nat.mul_add]
    have hh := position_card_le C
    omega
  · rw [Fintype.card_prod, Fintype.card_fin, test_card]
    ring
end AlphabetReduction
end MetricKMedian.PCP

end Inline_PCPBinaryReduction

end OAI
