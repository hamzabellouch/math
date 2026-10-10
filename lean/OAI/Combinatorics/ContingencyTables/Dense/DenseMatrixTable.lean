import OAI.Combinatorics.ContingencyTables.Machines.PreparedDenseCount
import OAI.Combinatorics.ContingencyTables.Machines.NatListEquality

namespace OAI

/-! # Constructing the actual dense transition matrix from its finite states -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

/-- Shared unary allowance and binary denominator, current exponent data,
and the enumeration of all states. -/
abbrev CountRowData := ((List Bool×ℕ)×FlatExponentData)×List (List ℕ)

def rowOffEntry (z : CountRowData×List ℕ) : ℕ :=
  preparedOffCount (z.1.1.1.1,(z.1.1.2,z.2))

def rowOffEntryRealizer : Realizer rowOffEntry :=
  composition (pair
    (composition (composition (composition first first) first) first)
    (pair (composition (composition first first) second) second)) preparedOffCountRealizer

lemma polynomial_rowOffEntry : PolynomialTime rowOffEntryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first)
    (polynomial_pair (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_second)) polynomial_preparedOffCount

def rowOffCounts (z : CountRowData) : List ℕ := z.2.map (fun b => rowOffEntry (z,b))

def rowOffCountsRealizer : Realizer rowOffCounts :=
  composition (pair identity second) (mapWith rowOffEntryRealizer)

lemma polynomial_rowOffCounts : PolynomialTime rowOffCountsRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_second)
    (polynomial_mapWith polynomial_rowOffEntry)

def rowEntry (z : CountRowData×List ℕ) : ℕ :=
  if NatListEquality.listEqual (z.1.1.2.1.2,z.2) then
    z.1.1.1.2-(rowOffCounts z.1).sum else rowOffEntry z

def rowEntryRealizer : Realizer rowEntry := by
  let current : Realizer (fun z : CountRowData×List ℕ => z.1.1.2.1.2) :=
    composition (composition (composition (composition first first) second) first) second
  let Q : Realizer (fun z : CountRowData×List ℕ => z.1.1.1.2) :=
    composition (composition (composition first first) first) second
  let total := composition (composition
    (first (A := CountRowData) (B := List ℕ)) rowOffCountsRealizer) listSum
  exact choose (composition (pair current second) NatListEquality.listEqualRealizer)
    (composition (pair Q total) subtract) rowOffEntryRealizer

lemma polynomial_rowEntry : PolynomialTime rowEntryRealizer := by
  have hc : PolynomialTime (composition (composition (composition
      (composition (first (A := CountRowData) (B := List ℕ)) first) second) first) second) :=
    polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_first)
      polynomial_second
  have hQ : PolynomialTime (composition (composition (composition
      (first (A := CountRowData) (B := List ℕ)) first) first) second) :=
    polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second
  unfold rowEntryRealizer
  exact polynomial_choose (polynomial_composition (polynomial_pair hc polynomial_second)
    NatListEquality.polynomial_listEqual)
    (polynomial_composition (polynomial_pair hQ
      (polynomial_composition (polynomial_composition polynomial_first polynomial_rowOffCounts)
        polynomial_listSum)) polynomial_subtract) polynomial_rowOffEntry

lemma rowEntry_actual {m n d N : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hq : m*n≤d)
    (e : Fin N ≃ Grid (I := Fin (m*n)) (4*d^8))
    (xs : List Bool) (hxs : xs.length=8*d^5)
    (a b : Grid (I := Fin (m*n)) (4*d^8)) :
    rowEntry (((((xs,2^denseStepBits d),
      (((marginCode R,marginCode P),gridNatCode a),d)),
      List.ofFn (fun i => gridNatCode (e i)))),gridNatCode b)=
        denseTransitionCount R P d finProdFinEquiv a b := by
  have hoff (b : Grid (I := Fin (m*n)) (4*d^8)) :
      rowOffEntry (((((xs,2^denseStepBits d),
        (((marginCode R,marginCode P),gridNatCode a),d)),
        List.ofFn (fun i => gridNatCode (e i)))),gridNatCode b)=
      FiniteAcceptCounts.offCount a
        (fun z : Fin (2^Nat.clog 2 (8*d)) => axisCodeStep a z)
        (fun b => denseExponent R P d finProdFinEquiv b-
          denseExponent R P d finProdFinEquiv a) (8*d^5) b := by
    unfold rowOffEntry
    rw [preparedOffCount_eq xs _ hxs]
    exact offCountCode_actual R P hq a b
  have hs : (rowOffCounts ((((xs,2^denseStepBits d),
      (((marginCode R,marginCode P),gridNatCode a),d)),
      List.ofFn (fun i => gridNatCode (e i))))).sum=
      ∑ b,FiniteAcceptCounts.offCount a
        (fun z : Fin (2^Nat.clog 2 (8*d)) => axisCodeStep a z)
        (fun b => denseExponent R P d finProdFinEquiv b-
          denseExponent R P d finProdFinEquiv a) (8*d^5) b := by
    simp only [rowOffCounts,List.map_ofFn,Function.comp_apply,hoff,List.sum_ofFn]
    exact e.sum_comp _
  have he : NatListEquality.listEqual (gridNatCode a,gridNatCode b)=true ↔ a=b := by
    rw [NatListEquality.listEqual_true]
    exact ⟨fun h => gridNatCode_injective h,fun h => congrArg gridNatCode h⟩
  unfold rowEntry denseTransitionCount FiniteAcceptCounts.row
  rw [hs,hoff]
  by_cases hab : a=b
  · subst b
    have hh : FiniteAcceptCounts.offCount a
        (fun z : Fin (2^Nat.clog 2 (8*d)) => axisCodeStep a z)
        (fun b => denseExponent R P d finProdFinEquiv b-
          denseExponent R P d finProdFinEquiv a) (8*d^5) a=0 := by
      simp [FiniteAcceptCounts.offCount]
    simp [he,hh,FiniteAcceptCounts.denominator,denseStepBits,pow_add]
  · have hh : NatListEquality.listEqual (gridNatCode a,gridNatCode b)=false :=
      Bool.eq_false_iff.mpr (fun h => hab (he.mp h))
    simp [hh,Ne.symm hab]

end ContingencyTables.DensePrograms

end OAI
