import OAI.NumberTheory.Ostmann.Construction.HistoryGiantSources
import OAI.NumberTheory.Ostmann.Arithmetic.SampledHistoryRate
import OAI.NumberTheory.Ostmann.Arithmetic.SingleFrequencyModulus

namespace OAI

/-! # The constructed adaptive support for actual forward giant coefficients -/

namespace Ostmann

open scoped Classical

def forwardNodeGiants (n : ℕ) (XL XR : ℤ) (p : Fin (2 ^ n - 1) → ℤ)
    (j : Fin (2 ^ n - 1)) : ℤ × ℤ :=
  ((historyGiantSources XL XR (preorderNodePath n j)).1.nodeValue n j p
      (historyGiantSources_known XL XR _).1,
    (historyGiantSources XL XR (preorderNodePath n j)).2.nodeValue n j p
      (historyGiantSources_known XL XR _).2)

/-- The actual node equations use the fixed nonbulk factor and the current
giant on each child. The support includes both coefficient unit conditions. -/
def forwardIntegerHistory (S : Finset ℤ) (n Q : ℕ) (t : FrequencyTree S n)
    (XL XR : ℤ) (CL CR : List Bool → ℤ) (a : SampledPivotHistory n Q) : Prop :=
  ∀ j : Fin (2 ^ n - 1),
    let f := singleTreeNodeFrequencies S n t j.val
    let path := preorderNodePath n j
    let g := forwardNodeGiants n XL XR a.pivots j
    f.left * (CR path * g.2) * a.rightProduct j -
      f.right * (CL path * g.1) * a.leftProduct j = f.root * a.pivots j ∧
    IsCoprime (CR path * g.2) f.root ∧ IsCoprime (CL path * g.1) f.root

theorem forwardIntegerHistory_valid (S : Finset ℤ) (n Q : ℕ) (t : FrequencyTree S n)
    (XL XR : ℤ) (CL CR : List Bool → ℤ) (a : SampledPivotHistory n Q)
    (ha : forwardIntegerHistory S n Q t XL XR CL CR a) :
    a.valid (forwardTreeAncestorScheme S n t XL XR CL CR) := by
  constructor
  · intro j
    rw [forwardTreeAncestorScheme_left, forwardTreeAncestorScheme_right]
    exact (ha j).1
  · intro j
    rw [forwardTreeAncestorScheme_left, forwardTreeAncestorScheme_right]
    exact (ha j).2

theorem forwardTreeAncestorScheme_depth (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (XL XR : ℤ) (CL CR : List Bool → ℤ) (j : Fin (2 ^ n - 1)) :
    (forwardTreeAncestorScheme S n t XL XR CL CR).depth j ≤ n :=
  (preorderNodePath_length n j).le

theorem forwardTreeAncestorScheme_root_ne_zero (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (XL XR : ℤ) (CL CR : List Bool → ℤ) (hS : ∀ s ∈ S, s ≠ 0)
    (j : Fin (2 ^ n - 1)) :
    ((forwardTreeAncestorScheme S n t XL XR CL CR).frequencies j).root ≠ 0 :=
  hS _ (singleTreeNodeFrequencies_root_mem S n t j.val j.isLt)

theorem forwardTreeAncestorScheme_frequency_dvd (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (XL XR : ℤ) (CL CR : List Bool → ℤ) (j : Fin (2 ^ n - 1)) :
    ((forwardTreeAncestorScheme S n t XL XR CL CR).frequencies j).root.natAbs ∣
      historyFrequencyProduct S n t := by
  apply history_node_dvd_frequencyProduct S n t
  change singleTreeNodeFrequencies S n t j.val ∈ singleFrequencySplitList S n t
  rw [singleTreeNodeFrequencies, List.getD_eq_getElem _ _ (by
    simpa only [singleFrequencySplitList_length] using j.isLt)]
  exact List.getElem_mem _

end Ostmann

end OAI
