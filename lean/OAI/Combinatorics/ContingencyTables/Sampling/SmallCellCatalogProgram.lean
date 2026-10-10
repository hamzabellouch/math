import OAI.Combinatorics.ContingencyTables.Sampling.SmallCellIndexProgram
import OAI.Combinatorics.MatchingCount.Machines.TreeFiniteCollections

namespace OAI

/-! # Enumerating the actual small cells from binary margins -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

def pairAt (z : ℕ×ℕ) : ℕ×ℕ := (z.2/z.1,z.2%z.1)

def pairAtRealizer : Realizer pairAt :=
  composition (pair second first) (pair quotient remainder)

lemma polynomial_pairAt : PolynomialTime pairAtRealizer :=
  polynomial_composition (polynomial_pair polynomial_second polynomial_first)
    (polynomial_pair polynomial_quotient polynomial_remainder)

def cellPairCodes : Realizer (fun z : List ℕ×List ℕ =>
    List.range (z.1.length*z.2.length)) :=
  composition (composition (pair (composition first listLength)
    (composition second listLength)) multiply) range

lemma polynomial_cellPairCodes : PolynomialTime cellPairCodes := by
  apply polynomial_boundedRange (polynomial_composition
    (polynomial_pair (polynomial_composition polynomial_first polynomial_listLength)
      (polynomial_composition polynomial_second polynomial_listLength)) polynomial_multiply) (X^2)
  intro z
  have hr : z.1.length≤weight z :=
    (list_length_le_weight z.1).trans (by rw [weight_prod]; omega)
  have hc : z.2.length≤weight z :=
    (list_length_le_weight z.2).trans (by rw [weight_prod]; omega)
  simpa only [Function.comp_apply,eval_pow,eval_mul,eval_X,pow_two] using Nat.mul_le_mul hr hc

def cellPairs (z : List ℕ×List ℕ) : List (ℕ×ℕ) :=
  (List.range (z.1.length*z.2.length)).map (fun a => pairAt (z.2.length,a))

def cellPairsRealizer : Realizer cellPairs :=
  composition (pair (composition second listLength) cellPairCodes) (mapWith pairAtRealizer)

theorem polynomial_cellPairs : PolynomialTime cellPairsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_second polynomial_listLength) polynomial_cellPairCodes)
    (polynomial_mapWith polynomial_pairAt)

lemma mem_cellPairs (r c : List ℕ) (i j : ℕ) :
    (i,j)∈cellPairs (r,c) ↔ i<r.length ∧ j<c.length := by
  simp only [cellPairs,List.mem_map,List.mem_range,pairAt,Prod.mk.injEq]
  constructor
  · rintro ⟨a,ha,hi,hj⟩
    have hc : 0<c.length := by nlinarith
    exact ⟨hi ▸ ((Nat.div_lt_iff_lt_mul hc).mpr ha),hj ▸ Nat.mod_lt a hc⟩
  · rintro ⟨hi,hj⟩
    have hc : 0<c.length := Nat.zero_lt_of_lt hj
    refine ⟨i*c.length+j,by nlinarith,?_,?_⟩
    · rw [Nat.mul_comm i c.length,Nat.mul_add_div hc,Nat.div_eq_of_lt hj,add_zero]
    · simp only [Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_eq_of_lt hj]

abbrev CellCatalogInput := (List ℕ×List ℕ)×ℕ

def smallCellTest (z : CellCatalogInput×(ℕ×ℕ)) : Bool :=
  decide (z.1.1.1.getD z.2.1 0<z.1.2 ∨ z.1.1.2.getD z.2.2 0<z.1.2)

def smallCellTestRealizer : Realizer smallCellTest := by
  let R : Realizer (fun z : CellCatalogInput×(ℕ×ℕ) => z.1.1.1.getD z.2.1 0) :=
    composition (pair (composition (composition first first) first)
      (composition second first)) (getDFast 0)
  let C : Realizer (fun z : CellCatalogInput×(ℕ×ℕ) => z.1.1.2.getD z.2.2 0) :=
    composition (pair (composition (composition first first) second)
      (composition second second)) (getDFast 0)
  let U : Realizer (fun z : CellCatalogInput×(ℕ×ℕ) => z.1.2) := composition first second
  exact (choose (composition (pair R U) less) (constant true)
    (composition (pair C U) less)).congr (by
      intro z
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply,decide_eq_true_eq,smallCellTest]
      split_ifs <;> simp_all)

lemma polynomial_smallCellTest : PolynomialTime smallCellTestRealizer := by
  unfold smallCellTestRealizer
  apply polynomial_congr
  apply polynomial_choose
  · exact polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
        (polynomial_composition polynomial_second polynomial_first)) (polynomial_getDFast 0))
      (polynomial_composition polynomial_first polynomial_second)) polynomial_less
  · exact polynomial_constant true
  · exact polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
        (polynomial_composition polynomial_second polynomial_second)) (polynomial_getDFast 0))
      (polynomial_composition polynomial_first polynomial_second)) polynomial_less

def smallCellCatalog (z : CellCatalogInput) : List (ℕ×ℕ) :=
  (cellPairs z.1).filter (fun a => smallCellTest (z,a))

def smallCellCatalogRealizer : Realizer smallCellCatalog :=
  composition (pair identity (composition first cellPairsRealizer)) (filterWith smallCellTestRealizer)

theorem polynomial_smallCellCatalog : PolynomialTime smallCellCatalogRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_cellPairs))
    (polynomial_filterWith polynomial_smallCellTest)

theorem mem_smallCellCatalog (r c : List ℕ) (U i j : ℕ) :
    (i,j)∈smallCellCatalog ((r,c),U) ↔
      i<r.length ∧ j<c.length ∧ (r.getD i 0<U ∨ c.getD j 0<U) := by
  simp only [smallCellCatalog,List.mem_filter,mem_cellPairs,smallCellTest,decide_eq_true_eq]
  tauto

end ContingencyTables.ProfilePrograms

end OAI
