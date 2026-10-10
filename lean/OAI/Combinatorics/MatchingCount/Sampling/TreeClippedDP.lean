import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeDPCount
import OAI.Combinatorics.MatchingCount.Sampling.TreeFastDPEntry
import OAI.Combinatorics.MatchingCount.Complexity.TreePolynomialGrid

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped Polynomial

def nVertices (o : CountInput) : ℕ := o.1.1.length
def nLabels (o : CountInput) : ℕ := o.1.2.length
def nPlan (o : CountInput) : ℕ := o.2.length
def BInitial (o : CountInput) : ℕ := nVertices o*nLabels o
def capBits (o : CountInput) : ℕ := nVertices o*nPlan o+(BInitial o)^2*nLabels o+1

def nVerticesRealizer : Realizer nVertices := composition first.fst listLength
def nLabelsRealizer : Realizer nLabels := composition first.snd listLength
def nPlanRealizer : Realizer nPlan := composition second listLength
def BInitialRealizer : Realizer BInitial := composition (pair nVerticesRealizer nLabelsRealizer) multiply
def capBitsRealizer : Realizer capBits := by
  let b:= BInitialRealizer
  let q:= composition (pair b b) multiply
  let v:= composition (pair q nLabelsRealizer) multiply
  let w:= composition (pair nVerticesRealizer nPlanRealizer) multiply
  exact (composition (composition (pair w v) add) successor).congr (by intro o; simp only [capBits,pow_two]; rfl)
lemma polynomial_nVertices : PolynomialTime nVerticesRealizer := by unfold nVerticesRealizer; exact polynomial_composition (polynomial_fst polynomial_first) polynomial_listLength
lemma polynomial_nLabels : PolynomialTime nLabelsRealizer := by unfold nLabelsRealizer; exact polynomial_composition (polynomial_snd polynomial_first) polynomial_listLength
lemma polynomial_nPlan : PolynomialTime nPlanRealizer := by unfold nPlanRealizer; exact polynomial_composition polynomial_second polynomial_listLength
lemma polynomial_BInitial : PolynomialTime BInitialRealizer :=
  polynomial_composition (polynomial_pair polynomial_nVertices polynomial_nLabels) polynomial_multiply
lemma polynomial_capBits : PolynomialTime capBitsRealizer := by
  unfold capBitsRealizer
  dsimp only
  apply polynomial_congr
  apply polynomial_composition _ polynomial_successor
  apply polynomial_composition _ polynomial_add
  have := polynomial_BInitial
  have := polynomial_nVertices
  have := polynomial_nLabels
  have := polynomial_nPlan
  tree_poly
lemma input_lengths (o : CountInput) : nVertices o≤weight o ∧ nLabels o≤weight o ∧ nPlan o≤weight o := by
  refine ⟨(list_length_le_weight _).trans ((weight_fst o.1).trans (weight_fst o)),
    (list_length_le_weight _).trans ((weight_snd o.1).trans (weight_fst o)),
    (list_length_le_weight _).trans (weight_snd o)⟩
lemma BInitial_bound (o : CountInput) : BInitial o≤(weight o)^2 := by
  obtain ⟨hn,hm,_⟩:=input_lengths o
  exact (Nat.mul_le_mul hn hm).trans_eq (pow_two _).symm
lemma capBits_bound (o : CountInput) : capBits o≤(weight o)^2+(weight o)^5+1 := by
  obtain ⟨hn,hm,hL⟩:=input_lengths o
  have hB:=BInitial_bound o
  have h1:=Nat.mul_le_mul hn hL
  have h2:=Nat.mul_le_mul (Nat.pow_le_pow_left hB 2) hm
  calc
    _ ≤ weight o*weight o+((weight o)^2)^2*weight o+1 := by unfold capBits; omega
    _ = _ := by ring

def initialEntry (x : CountInput×(ℕ×ℕ)) : ℕ := UnitRefresh.pairingCount (min x.2.2 (BInitial x.1))
def initialEntryRealizer : Realizer initialEntry :=
  composition (composition (pair second.snd (composition first BInitialRealizer)) minNat) pairingNumber
lemma polynomial_initialEntry : PolynomialTime initialEntryRealizer := by
  unfold initialEntryRealizer
  refine polynomial_boundedPairingNumber ?_ (X^2) ?_
  · apply polynomial_composition _ polynomial_minNat
    apply polynomial_pair (polynomial_snd polynomial_second) (polynomial_composition polynomial_first polynomial_BInitial)
  · intro x
    simp only [Polynomial.eval_pow,Polynomial.eval_X]
    exact (min_le_right _ _).trans ((BInitial_bound x.1).trans (Nat.pow_le_pow_left (weight_fst x) 2))
def initialFast : Realizer (fun o : CountInput=>initial (nLabels o,BInitial o)) :=
  (grid nLabelsRealizer BInitialRealizer initialEntryRealizer).congr (by
    intro o
    unfold tabulate initial initialEntry
    apply List.map_congr_left
    intro a _row_mem
    apply List.map_congr_left
    intro r hr
    have hh : r≤BInitial o := by have :=List.mem_range.mp hr; dsimp only at this; omega
    simp only [Nat.min_eq_left hh])
lemma polynomial_initialFast : PolynomialTime initialFast := by
  unfold initialFast
  apply polynomial_congr
  exact polynomial_grid polynomial_nLabels polynomial_BInitial polynomial_initialEntry X (X^2)
    (fun o=>by simpa using (input_lengths o).2.1) (fun o=>by simpa using BInitial_bound o)

abbrev UpdateInput := (CountInput×RawCtx)×ℕ
def updateRows (x : UpdateInput) := nLabels x.1.1
def updateColumns (x : UpdateInput) := nVertices x.1.1*min x.2 (nPlan x.1.1)
def updateRowsRealizer : Realizer updateRows := composition first.fst nLabelsRealizer
def updateColumnsRealizer : Realizer updateColumns :=
  composition (pair (composition first.fst nVerticesRealizer)
    (composition (pair second (composition first.fst nPlanRealizer)) minNat)) multiply
lemma polynomial_updateRows : PolynomialTime updateRowsRealizer :=
  polynomial_composition (polynomial_fst polynomial_first) polynomial_nLabels
lemma polynomial_updateColumns : PolynomialTime updateColumnsRealizer := by
  unfold updateColumnsRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_fst polynomial_first) polynomial_nVertices)
    (polynomial_composition (polynomial_pair polynomial_second
      (polynomial_composition (polynomial_fst polynomial_first) polynomial_nPlan)) polynomial_minNat)) polynomial_multiply
lemma update_dimensions (x : UpdateInput) : updateRows x≤weight x ∧ updateColumns x≤(weight x)^2 := by
  have hwo:weight x.1.1≤weight x := (weight_fst x.1).trans (weight_fst x)
  obtain ⟨hn,hm,hL⟩:=input_lengths x.1.1
  refine ⟨hm.trans hwo,?_⟩
  exact (Nat.mul_le_mul (hn.trans hwo) ((min_le_right _ _).trans (hL.trans hwo))).trans_eq (pow_two _).symm

def cappedEntry (x : UpdateInput×(ℕ×ℕ)) : ℕ := clip (capBits x.1.1.1,rawEntry (x.1.1.2,x.2))
def cappedEntryRealizer : Realizer cappedEntry :=
  (composition (pair (composition first.fst.fst capBitsRealizer)
    (composition (pair first.fst.snd second) rawEntryRealizer)) clipRealizer).congr (fun _=>rfl)
lemma polynomial_cappedEntry : PolynomialTime cappedEntryRealizer := by
  unfold cappedEntryRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  apply polynomial_composition _ polynomial_clip
  apply polynomial_pair
  · apply polynomial_composition _ polynomial_capBits
    tree_poly
  · apply polynomial_composition _ polynomial_rawEntry
    tree_poly

def cappedUpdate (x : UpdateInput) : Table := tabulate cappedEntry (x,(updateRows x,updateColumns x))
def cappedUpdateRealizer : Realizer cappedUpdate := grid updateRowsRealizer updateColumnsRealizer cappedEntryRealizer
lemma polynomial_cappedUpdate : PolynomialTime cappedUpdateRealizer :=
  polynomial_grid polynomial_updateRows polynomial_updateColumns polynomial_cappedEntry X (X^2)
    (fun x=>by simpa using (update_dimensions x).1) (fun x=>by simpa using (update_dimensions x).2)

end MatchingFPRAS.ExecutableDP

end OAI
