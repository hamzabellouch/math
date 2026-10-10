import OAI.NumberTheory.Ostmann.Arithmetic.FrequencyModelAdaptiveSupport
import OAI.NumberTheory.Ostmann.Tree.PairedFrequencyProjection
import OAI.NumberTheory.Ostmann.Arithmetic.VariableModulusSupport

namespace OAI

/-! # Paired support for the two actual arithmetic frequency gates -/

namespace Ostmann
open scoped Classical

noncomputable def frequencyModelPairData {σ : Type*} (value : σ → ℕ)
    (S : Finset ℤ) (n R : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ b (j : Fin (2 ^ n - 1)),
    (singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val).root.natAbs ∣ R)
    (small : Bool → TreeLeafTuple (List σ) n) (a : Bool → MovingSampleSlots σ n) (x y : ℤ)
    (total : (ZMod (R ^ (n - 1 + 2)))ˣ) (past : List (ZMod (R ^ (n - 1 + 2)))ˣ) :
    Option (ArithmeticSplitData (R ^ (n - 1 + 2)) × ArithmeticSplitData (R ^ (n - 1 + 2))) :=
  pairArithmeticData
    (frequencyModelAdaptiveData value S n R (frequencyPairProjection S n false t)
      hS (hR false) (small false) (a false) x y total past)
    (frequencyModelAdaptiveData value S n R (frequencyPairProjection S n true t)
      hS (hR true) (small true) (a true) x y total past)

theorem frequencyModelPairData_frequencies {σ : Type*} (value : σ → ℕ)
    (S : Finset ℤ) (n R : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ b (j : Fin (2 ^ n - 1)),
    (singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val).root.natAbs ∣ R)
    (small : Bool → TreeLeafTuple (List σ) n) (a : Bool → MovingSampleSlots σ n) (x y : ℤ)
    (total : (ZMod (R ^ (n - 1 + 2)))ˣ) (past : List (ZMod (R ^ (n - 1 + 2)))ˣ)
    (d e : ArithmeticSplitData (R ^ (n - 1 + 2)))
    (hde : frequencyModelPairData value S n R t hS hR small a x y total past = some (d, e)) :
    d.hasFrequencies (treeNodeFrequencies S n t past.length).1 ∧
      e.hasFrequencies (treeNodeFrequencies S n t past.length).2 := by
  let A := fun b => frequencyModelAdaptiveData value S n R (frequencyPairProjection S n b t)
    hS (hR b) (small b) (a b) x y total past
  change pairArithmeticData (A false) (A true) = some (d, e) at hde
  cases hd : A false with
  | none => simp [pairArithmeticData, hd] at hde
  | some d' =>
    cases he : A true with
    | none => simp [pairArithmeticData, he] at hde
    | some e' =>
      have h : d' = d ∧ e' = e := by
        simpa only [pairArithmeticData, hd, he, Option.some.injEq, Prod.mk.injEq] using hde
      rcases h with ⟨rfl, rfl⟩
      have hL := frequencyModelAdaptiveData_frequencies value S n R
        (frequencyPairProjection S n false t) hS (hR false) (small false) (a false) x y total past d' hd
      have hR' := frequencyModelAdaptiveData_frequencies value S n R
        (frequencyPairProjection S n true t) hS (hR true) (small true) (a true) x y total past e' he
      simpa only [treeNodeFrequencies_projection, Bool.false_eq_true, ite_false, ite_true]
        using And.intro hL hR'

/-- The same tuple of bulk residues tests both histories, under the original
unit law. Only the two frequency gates are hypotheses. -/
theorem frequencyModelPairData_support {σ : Type*} (value : σ → ℕ)
    (S : Finset ℤ) (n R : ℕ) [NeZero (R ^ (n - 1 + 2))] (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ b (j : Fin (2 ^ n - 1)),
    (singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val).root.natAbs ∣ R)
    (small : Bool → TreeLeafTuple (List σ) n) (bulk : TreeLeafTuple (List σ) n)
    (a : Bool → MovingSampleSlots σ n) (x y : ℤ)
    (hsmall : ∀ i, IsCoprime (value i : ℤ) (R : ℤ))
    (z : TreeLeafTuple (ZMod (R ^ (n - 1 + 2)))ˣ n)
    (hz : treeIntegerResidues (R ^ (n - 1 + 2)) n
      (treeLeafMap (fun q : ℕ => (q : ℤ)) n (movingSlotValues value n bulk)) z)
    (hg : ∀ b, movingFrequencyGate value R
      (buildMovingSlotData n
        (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
        (small b) bulk (a b)) x y) :
    arithmeticLeafSupport n (frequencyModelPairData value S n R t hS hR small a x y) z = 1 := by
  change arithmeticLeafSupport n (fun total past => pairArithmeticData
    (frequencyModelAdaptiveData value S n R (frequencyPairProjection S n false t)
      hS (hR false) (small false) (a false) x y total past)
    (frequencyModelAdaptiveData value S n R (frequencyPairProjection S n true t)
      hS (hR true) (small true) (a true) x y total past)) z = 1
  rw [arithmeticLeafSupport_pair,
    frequencyModelAdaptiveData_support value S n R (frequencyPairProjection S n false t)
      hS (hR false) (small false) bulk (a false) x y hsmall z hz (hg false),
    frequencyModelAdaptiveData_support value S n R (frequencyPairProjection S n true t)
      hS (hR true) (small true) bulk (a true) x y hsmall z hz (hg true), one_mul]

end Ostmann

end OAI
