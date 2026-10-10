import OAI.NumberTheory.Ostmann.Construction.AncestorPivotPrecision
import OAI.NumberTheory.Ostmann.Characters.TreeSplitResidues
import OAI.NumberTheory.Ostmann.Arithmetic.IntegerResidueSplit

namespace OAI

/-! # Constructing coefficients from the already exposed product prefix -/

namespace Ostmann

open scoped Classical

/-- Actual integer products together with their exact unit residues. -/
structure SampledPivotHistory (n Q : ℕ) where
  bulk : TreeLeafTuple ℤ n
  residue : TreeLeafTuple (ZMod Q)ˣ n
  pivots : Fin (2 ^ n - 1) → ℤ
  compatible : treeIntegerResidues Q n bulk residue

def SampledPivotHistory.leftProduct {n Q : ℕ} (a : SampledPivotHistory n Q)
    (j : Fin (2 ^ n - 1)) : ℤ := ((actualChildProducts n a.bulk).getD j.val (1, 1)).1

def SampledPivotHistory.rightProduct {n Q : ℕ} (a : SampledPivotHistory n Q)
    (j : Fin (2 ^ n - 1)) : ℤ := ((actualChildProducts n a.bulk).getD j.val (1, 1)).2

def SampledPivotHistory.valid {n Q : ℕ} (a : SampledPivotHistory n Q)
    (D : PivotDependencyScheme (2 ^ n - 1)) : Prop :=
  D.equations a.leftProduct a.rightProduct a.pivots ∧
    ∀ j, IsCoprime (D.leftCoefficient a.pivots j) (D.frequencies j).root ∧
      IsCoprime (D.rightCoefficient a.pivots j) (D.frequencies j).root

def SampledPivotHistory.matches {n Q : ℕ} (a : SampledPivotHistory n Q)
    (total : (ZMod Q)ˣ) (past : List (ZMod Q)ˣ) : Prop :=
  treeLeafProduct n a.residue = total ∧
    ((actualSplitValues n a.residue).take past.length).reverse = past

/-- Choose any valid completion of the exposed prefix. The precision theorem
below proves that the required reduced coefficients do not depend on it. -/
noncomputable def adaptivePivotCoefficients (n Q : ℕ)
    (D : PivotDependencyScheme (2 ^ n - 1))
    (total : (ZMod Q)ˣ) (past : List (ZMod Q)ˣ) : ZMod Q × ZMod Q :=
  if hj : past.length < 2 ^ n - 1 then
    if h : ∃ a : SampledPivotHistory n Q, a.valid D ∧ a.matches total past then
      let a := Classical.choose h
      (D.leftCoefficient a.pivots ⟨past.length, hj⟩,
        D.rightCoefficient a.pivots ⟨past.length, hj⟩)
    else (0, 0)
  else (0, 0)

theorem adaptivePivotCoefficients_witness (n Q : ℕ)
    (D : PivotDependencyScheme (2 ^ n - 1))
    (total : (ZMod Q)ˣ) (past : List (ZMod Q)ˣ)
    (hj : past.length < 2 ^ n - 1)
    (hex : ∃ a : SampledPivotHistory n Q, a.valid D ∧ a.matches total past) :
    ∃ a : SampledPivotHistory n Q, a.valid D ∧ a.matches total past ∧
      adaptivePivotCoefficients n Q D total past =
        ((D.leftCoefficient a.pivots ⟨past.length, hj⟩ : ZMod Q),
          (D.rightCoefficient a.pivots ⟨past.length, hj⟩ : ZMod Q)) := by
  refine ⟨Classical.choose hex, (Classical.choose_spec hex).1, (Classical.choose_spec hex).2, ?_⟩
  simp only [adaptivePivotCoefficients, dite_eq_left hj, dite_eq_left hex]

/-- Two completions of one prefix agree on the bulk products at every
previously exposed node. -/
theorem SampledPivotHistory.prefix_products {n Q : ℕ}
    (a b : SampledPivotHistory n Q) (total : (ZMod Q)ˣ) (past : List (ZMod Q)ˣ)
    (ha : a.matches total past) (hb : b.matches total past)
    (hj : past.length ≤ 2 ^ n - 1) (i : Fin (2 ^ n - 1)) (hi : i.val < past.length) :
    (a.leftProduct i : ZMod Q) = b.leftProduct i ∧
      (a.rightProduct i : ZMod Q) = b.rightProduct i := by
  have hpre : (actualSplitValues n a.residue).take past.length =
      (actualSplitValues n b.residue).take past.length := by
    exact List.reverse_injective (ha.2.trans hb.2.symm)
  have hc := exposed_prefix_children_eq n a.residue b.residue past.length
    (ha.1.trans hb.1.symm) hpre i.val hi hj
  have hca := treeIntegerResidues_child Q n a.bulk a.residue a.compatible i.val
  have hcb := treeIntegerResidues_child Q n b.bulk b.residue b.compatible i.val
  refine ⟨?_, ?_⟩
  · exact hca.1.symm.trans ((congrArg (fun p => (p.1 : ZMod Q)) hc).trans hcb.1)
  · exact hca.2.symm.trans ((congrArg (fun p => (p.2 : ZMod Q)) hc).trans hcb.2)

/-- The chosen completion gives the actual coefficients modulo the current
root frequency, even though its integer pivots may differ. -/
theorem adaptivePivotCoefficients_reduce (n R k : ℕ)
    (D : PivotDependencyScheme (2 ^ n - 1))
    (hdepth : ∀ i, D.depth i ≤ k) (hs : ∀ i, (D.frequencies i).root ≠ 0)
    (hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (a : SampledPivotHistory n (R ^ (k + 2))) (ha : a.valid D)
    (total : (ZMod (R ^ (k + 2)))ˣ) (past : List (ZMod (R ^ (k + 2)))ˣ)
    (hm : a.matches total past) (hj : past.length < 2 ^ n - 1) :
    let j : Fin (2 ^ n - 1) := ⟨past.length, hj⟩
    let hd : (D.frequencies j).root.natAbs ∣ R ^ (k + 2) :=
      (hsR j).trans (dvd_pow_self R (by omega))
    ZMod.castHom hd (ZMod (D.frequencies j).root.natAbs)
        (adaptivePivotCoefficients n (R ^ (k + 2)) D total past).1 =
        D.leftCoefficient a.pivots j ∧
      ZMod.castHom hd (ZMod (D.frequencies j).root.natAbs)
        (adaptivePivotCoefficients n (R ^ (k + 2)) D total past).2 =
        D.rightCoefficient a.pivots j := by
  dsimp only
  obtain ⟨b, hb, hbm, hcoeff⟩ := adaptivePivotCoefficients_witness n (R ^ (k + 2)) D total past hj
    ⟨a, ha, hm⟩
  have hprod (i : Fin (2 ^ n - 1)) (hi : i.val < past.length) :=
    b.prefix_products a total past hbm hm (Nat.le_of_lt hj) i hi
  have hL (i : Fin (2 ^ n - 1)) (hi : i.val < past.length) :
      b.leftProduct i ≡ a.leftProduct i [ZMOD (R : ℤ) ^ (k + 2)] := by
    have h := (ZMod.intCast_eq_intCast_iff _ _ _).mp (hprod i hi).1
    simpa only [Nat.cast_pow] using h
  have hR (i : Fin (2 ^ n - 1)) (hi : i.val < past.length) :
      b.rightProduct i ≡ a.rightProduct i [ZMOD (R : ℤ) ^ (k + 2)] := by
    have h := (ZMod.intCast_eq_intCast_iff _ _ _).mp (hprod i hi).2
    simpa only [Nat.cast_pow] using h
  have h := D.coefficients_prefix_precision R k ⟨past.length, hj⟩ hdepth hs hsR
    b.leftProduct b.rightProduct b.pivots a.leftProduct a.rightProduct a.pivots hb.1 ha.1 hL hR
  rw [hcoeff]
  simp only [map_intCast]
  exact ⟨(ZMod.intCast_eq_intCast_iff _ _ _).mpr h.1,
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr h.2⟩

end Ostmann

end OAI
