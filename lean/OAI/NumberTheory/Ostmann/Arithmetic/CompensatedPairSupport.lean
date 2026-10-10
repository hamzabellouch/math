import OAI.NumberTheory.Ostmann.Arithmetic.MovingAdaptiveSupport
import OAI.NumberTheory.Ostmann.Arithmetic.WeightedArithmeticSupport

namespace OAI

/-! # Paired adaptive support on the same original bulk variables -/

namespace Ostmann
open scoped Classical

def pairArithmeticData {Q : ℕ} (d e : Option (ArithmeticSplitData Q)) :
    Option (ArithmeticSplitData Q × ArithmeticSplitData Q) :=
  match d, e with
  | some d, some e => some (d, e)
  | _, _ => none

theorem pairArithmeticData_test {Q : ℕ} (d e : Option (ArithmeticSplitData Q))
    (x : (ZMod Q)ˣ) :
    arithmeticPairSplitTest (pairArithmeticData d e) x ↔
      singleArithmeticSplitTest d x ∧ singleArithmeticSplitTest e x := by
  cases d <;> cases e <;> simp [pairArithmeticData, arithmeticPairSplitTest, singleArithmeticSplitTest]

theorem sequentialSupport_and {A : Type} (p q : List A → A → Prop)
    (past : List A) (n : ℕ) (x : SplitSamples A n) :
    sequentialSupport (fun past y => p past y ∧ q past y) past n x =
      sequentialSupport p past n x * sequentialSupport q past n x := by
  induction n generalizing past with
  | zero => simp [sequentialSupport]
  | succ n ih =>
    simp only [sequentialSupport]
    by_cases hp : p past x.1 <;> by_cases hq : q past x.1 <;>
      simp only [hp, hq, and_self, and_true, and_false,
        ite_true, ite_false, zero_mul, mul_zero, ih]

theorem arithmeticLeafSupport_pair {Q : ℕ} [NeZero Q] (n : ℕ)
    (d e : (ZMod Q)ˣ → List (ZMod Q)ˣ → Option (ArithmeticSplitData Q))
    (x : TreeLeafTuple (ZMod Q)ˣ n) :
    arithmeticLeafSupport n (fun total past => pairArithmeticData (d total past) (e total past)) x =
      singleArithmeticLeafSupport n d x * singleArithmeticLeafSupport n e x := by
  unfold arithmeticLeafSupport singleArithmeticLeafSupport
  simp only [pairArithmeticData_test]
  exact sequentialSupport_and _ _ _ _ _

noncomputable def compensatedPairData (n R k : ℕ)
    (D E : PivotDependencyScheme (2 ^ n - 1)) (U V : Fin (2 ^ n - 1) → ℤ)
    (hD : ∀ i, (D.frequencies i).root ≠ 0) (hE : ∀ i, (E.frequencies i).root ≠ 0)
    (hDR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (hER : ∀ i, (E.frequencies i).root.natAbs ∣ R)
    (total : (ZMod (R ^ (k + 2)))ˣ) (past : List (ZMod (R ^ (k + 2)))ˣ) :
    Option (ArithmeticSplitData (R ^ (k + 2)) × ArithmeticSplitData (R ^ (k + 2))) :=
  pairArithmeticData (compensatedAdaptiveData n R k D U hD hDR total past)
    (compensatedAdaptiveData n R k E V hE hER total past)

theorem compensatedPairData_frequencies (n R k : ℕ)
    (D E : PivotDependencyScheme (2 ^ n - 1)) (U V : Fin (2 ^ n - 1) → ℤ)
    (hD : ∀ i, (D.frequencies i).root ≠ 0) (hE : ∀ i, (E.frequencies i).root ≠ 0)
    (hDR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (hER : ∀ i, (E.frequencies i).root.natAbs ∣ R)
    (total : (ZMod (R ^ (k + 2)))ˣ) (past : List (ZMod (R ^ (k + 2)))ˣ)
    (hj : past.length < 2 ^ n - 1) (d e : ArithmeticSplitData (R ^ (k + 2)))
    (hde : compensatedPairData n R k D E U V hD hE hDR hER total past = some (d, e)) :
    d.hasFrequencies (D.frequencies ⟨past.length, hj⟩) ∧
      e.hasFrequencies (E.frequencies ⟨past.length, hj⟩) := by
  cases hd : compensatedAdaptiveData n R k D U hD hDR total past with
  | none => simp [compensatedPairData, pairArithmeticData, hd] at hde
  | some d' =>
    cases he : compensatedAdaptiveData n R k E V hE hER total past with
    | none => simp [compensatedPairData, pairArithmeticData, he] at hde
    | some e' =>
      have h : d' = d ∧ e' = e := by
        simpa only [compensatedPairData, pairArithmeticData, hd, he,
          Option.some.injEq, Prod.mk.injEq] using hde
      rcases h with ⟨rfl, rfl⟩
      exact ⟨compensatedAdaptiveData_frequencies n R k D U hD hDR total past hj d' hd,
        compensatedAdaptiveData_frequencies n R k E V hE hER total past hj e' he⟩

/-- Both histories use one bulk residue tuple; no history validity is used
as a conditioning event. -/
theorem compensatedPairData_actual_support (n R k : ℕ) [NeZero (R ^ (k + 2))]
    (D E : PivotDependencyScheme (2 ^ n - 1)) (U V : Fin (2 ^ n - 1) → ℤ)
    (hU : ∀ i, IsCoprime (U i) (R : ℤ)) (hV : ∀ i, IsCoprime (V i) (R : ℤ))
    (hdepthD : ∀ i, D.depth i ≤ k) (hdepthE : ∀ i, E.depth i ≤ k)
    (hD : ∀ i, (D.frequencies i).root ≠ 0) (hE : ∀ i, (E.frequencies i).root ≠ 0)
    (hDR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (hER : ∀ i, (E.frequencies i).root.natAbs ∣ R)
    (a b : SampledPivotHistory n (R ^ (k + 2)))
    (ha : a.compensatedValid D U) (hb : b.compensatedValid E V) (hab : a.residue = b.residue) :
    arithmeticLeafSupport n (compensatedPairData n R k D E U V hD hE hDR hER) a.residue = 1 := by
  change arithmeticLeafSupport n
    (fun total past => pairArithmeticData
      (compensatedAdaptiveData n R k D U hD hDR total past)
      (compensatedAdaptiveData n R k E V hE hER total past)) a.residue = 1
  rw [arithmeticLeafSupport_pair,
    compensatedAdaptiveData_actual_support n R k D U hU hdepthD hD hDR a ha,
    hab, compensatedAdaptiveData_actual_support n R k E V hV hdepthE hE hER b hb, one_mul]

end Ostmann

end OAI
