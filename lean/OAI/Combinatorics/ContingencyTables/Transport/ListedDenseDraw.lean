import OAI.Combinatorics.ContingencyTables.Transport.ListedCompletion
import OAI.Combinatorics.ContingencyTables.Transport.ReferenceDrawBounds
import OAI.Combinatorics.ContingencyTables.Machines.ResidualDenseProgram

namespace OAI

/-! # A canonical dense draw in the actual retained completion fibre -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open CompletionCounts PaddedCompletions ResidualMixture FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}
variable (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)

abbrev largeTailCount {m : ℕ} (r : Fin m → ℕ) (V : ℕ) : ℕ :=
  (largeIndices (V,List.ofFn r)).length-1

local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "U" => d^20
local notation "L" => d^12
local notation "R" => listedRows r c U L (stateCapacity r c) hr
local notation "P" => listedColumns r c U L (stateCapacity r c) hc
local notation "nr" => largeTailCount r U
local notation "nc" => largeTailCount c U

lemma largeIndices_length_le {m : ℕ} (r : Fin m → ℕ) (V : ℕ) :
    (largeIndices (V,List.ofFn r)).length ≤ m := by
  have h := Fintype.card_congr (largeIndexEquiv r V)
  rw [Fintype.card_fin] at h
  rw [h]
  exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin m)

include hr hc in
lemma listed_dimensions :
    Fintype.card (Option (Fin nr)) ≤ d ∧
    Fintype.card (Option (Fin nc)) ≤ d ∧ Fintype.card (Fin nr×Fin nc) ≤ d := by
  have hm := largeIndices_length_le r U
  have hn := largeIndices_length_le c U
  simp only [Fintype.card_option,Fintype.card_fin,Fintype.card_prod,largeTailCount]
  have hmul := Nat.mul_le_mul ((Nat.sub_le (largeIndices (U,List.ofFn r)).length 1).trans hm)
    ((Nat.sub_le (largeIndices (U,List.ofFn c)).length 1).trans hn)
  have hd := dimension_le_allowance (I := Fin m) (J := Fin n)
  simp only [Fintype.card_fin] at hd
  have hdr : m ≤ d := by unfold dimensionAllowance; simp only [Fintype.card_fin]; nlinarith
  have hdc : n ≤ d := by unfold dimensionAllowance; simp only [Fintype.card_fin]; nlinarith
  exact ⟨by omega,by omega,hmul.trans hd⟩

include hr hc in
lemma listed_dimension_fourteen : 14 ≤ d :=
  reference_dimension_fourteen r c U (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none)

abbrev paperListedEquiv (z : PaperStates r c) : PaperFibre r c z ≃ Table (R z) (P z) :=
  listedFibreEquiv r c U L (stateCapacity r c) hr hc z
    (physical_paper_capacity _ r c _ _ _ dimension_le_allowance z)

lemma listed_paper_totals (z : PaperStates r c) : (∑ i,R z i)=∑ j,P z j :=
  listed_totals r c U L (stateCapacity r c) hr hc z
    (physical_paper_capacity _ r c _ _ _ dimension_le_allowance z)

lemma listed_row_bound (z : PaperStates r c) (i : Option (Fin nr)) : R z i ≤ stateBound r c := by
  have h := reference_row_le_stateBound r c (largeOptionEquiv r U hr none) z
    (listedReferenceIndex r U hr i)
  have he := congrFun (listedReference_row r c U L (stateCapacity r c) hr z) i
  exact he ▸ h

abbrev listedDrawBits (h : ℕ) (z : PaperStates r c) := normalizedDrawBits (R z) (P z) d h

def listedDenseDraw (h : ℕ) (z : PaperStates r c)
    (bits : Fin (listedDrawBits r c hr hc h z) → Bool) : PaperFibre r c z :=
  (paperListedEquiv r c hr hc z).symm
    (normalizedBooleanDraw (R z) (P z) (listed_dimension_fourteen r c hr hc)
      (listed_row_padding r c U L (stateCapacity r c) hr hc z)
      (listed_column_padding r c U L (stateCapacity r c) hr hc z)
      (listed_paper_totals r c hr hc z) h
      (canonicalOrigin (nr*nc) d (by have := listed_dimension_fourteen r c hr hc; omega))
      (canonicalFallback (R z) (P z) (listed_paper_totals r c hr hc z)) bits)

theorem listedDrawBits_le (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
    (z : PaperStates r c) : listedDrawBits r c hr hc h z ≤ 25*(d+b+h+1)^62 := by
  apply normalizedDrawBits_polynomial (R z) (P z) d (stateBound r c) b h
  · simpa only [Fintype.card_prod,Fintype.card_fin] using (listed_dimensions r c hr hc).2.2
  · exact listed_row_bound r c hr z
  · exact hb

theorem listedDenseDraw_variation
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (nr*nc))
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin (nr*nc)) (4*d^8)))
    (h : ℕ) (z : PaperStates r c) :
    (variation (mapLaw (uniformLaw (α := Fin (listedDrawBits r c hr hc h z) → Bool))
      (listedDenseDraw r c hr hc h z)) (uniformLaw (α := PaperFibre r c z)):ℝ) ≤ (2:ℝ)^(-(h:ℝ)) := by
  let E : PaperFibre r c z ≃ Table (R z) (P z) := paperListedEquiv r c hr hc z
  let fb := canonicalFallback (R z) (P z) (listed_paper_totals r c hr hc z)
  let : Nonempty (Table (R z) (P z)) := ⟨fb⟩
  have hv := canonicalDenseDraw_variation (R z) (P z) (listed_dimension_fourteen r c hr hc)
    (listed_row_padding r c U L (stateCapacity r c) hr hc z)
    (listed_column_padding r c U L (stateCapacity r c) hr hc z)
    (listed_dimensions r c hr hc).1 (listed_dimensions r c hr hc).2.1
    (listed_dimensions r c hr hc).2.2 (listed_paper_totals r c hr hc z) hPL hCheeger h
  unfold listedDenseDraw
  rw [mapLaw_equiv_output]
  change (variation (equivLaw E.symm _) (uniformLaw (α := PaperFibre r c z)):ℝ) ≤ _
  rw [←uniform_equiv E.symm,variation_equiv]
  exact hv

end
end ContingencyTables.SmallGraphProfiles

end OAI
