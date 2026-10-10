import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalSubtractCorrect
import OAI.Analysis.MatrixSigning.Arithmetic.RationalDivisionMachine
import OAI.Analysis.MatrixSigning.Encoding.WireAppend

namespace OAI

section

namespace KS.W07.SchurCellMachine

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def workspace (input output x a b c : List Bool) : Fin 23 → List Bool :=
  fun j => if j = 0 then input else if j = 10 then output else if j = 19 then x
    else if j = 20 then a else if j = 21 then b else if j = 22 then c else []

def firstPorts (n : ℕ) (h : n ≤ 23) : Fin n ↪ Fin 23 := Fin.castLEEmb h

def extend {n : ℕ} (s : Fin n → List Bool) (spare : Fin 23 → List Bool) : Fin 23 → List Bool :=
  fun j => if h : j.val < n then s ⟨j.val, h⟩ else spare j

theorem first_spec {n : ℕ} (hn : n ≤ 23) (P : Program n)
    (before after : Fin n → List Bool) (spare : Fin 23 → List Bool) (ticks : ℕ)
    (h : RunSpec P before after ticks) :
    RunSpec (KS.W29.FixedSequential.liftPorts P (firstPorts n hn))
      (extend before spare) (extend after spare) ticks := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec P (firstPorts n hn) _ _ _ _ _ h
  · intro i; simp [extend, firstPorts, i.isLt]
  · intro i; simp [extend, firstPorts, i.isLt]
  · intro j hj
    by_cases hb : j.val < n
    · exact (hj ⟨j.val, hb⟩ (Fin.ext rfl)).elim
    · simp [extend, hb]

def preparePair (source target : Fin 23) : Program 23 :=
  compose (WireAppend.program source target 16) (WireAppend.program target 0 16)

def pairAfter (source target : Fin 23) (before : Fin 23 → List Bool) : Fin 23 → List Bool :=
  WireAppend.after target 0 (WireAppend.after source target before)

theorem preparePair_spec (source target : Fin 23)
    (hst : source ≠ target) (hs16 : source ≠ 16) (ht16 : target ≠ 16)
    (ht0 : target ≠ 0) (before : Fin 23 → List Bool) (he : before 16 = []) :
    RunSpec (preparePair source target) before (pairAfter source target before)
      (4 * (before source).length + 2 * (before target).length + 4) := by
  have h₁ := WireAppend.spec source target 16 hst hs16 (Ne.symm ht16) before he
  have hempty : WireAppend.after source target before 16 = [] := by
    simp [WireAppend.after, Ne.symm hs16, Ne.symm ht16, he]
  have h₂ := WireAppend.spec target 0 16 ht0 ht16 (by decide)
    (WireAppend.after source target before) hempty
  have h := h₁.compose h₂
  have hlen : (WireAppend.after source target before target).length =
      (before source).length + (before target).length := by
    simp [WireAppend.after, Ne.symm hst]
  simpa only [preparePair, pairAfter, hlen, Nat.mul_add,
    show 2 * (before source).length + 2 +
      (2 * (before source).length + 2 * (before target).length + 2) =
      4 * (before source).length + 2 * (before target).length + 4 by omega] using h

def multiply : Program 23 := KS.W29.FixedSequential.liftPorts
  KS.W15.RationalMultiply.program (firstPorts 13 (by decide))
def divide : Program 23 := KS.W29.FixedSequential.liftPorts
  KS.W30.RationalDivision.program (firstPorts 15 (by decide))
def subtract : Program 23 := KS.W29.FixedSequential.liftPorts
  KS.W13.RationalSubtract.program (firstPorts 19 (by decide))

def program : Program 23 := compose (preparePair 20 21)
  (compose multiply (compose (preparePair 10 22)
    (compose divide (compose (preparePair 19 10) subtract))))

def ticks (x a b c : ℚ) : ℕ :=
  (4 * KS.W01.ratLength a + 2 * KS.W01.ratLength b + 4) +
  (KS.W15.RationalMultiply.totalTicks a b +
  ((4 * KS.W01.ratLength (a * b) + 2 * KS.W01.ratLength c + 4) +
  (KS.W29.polynomialFuel 1100000 3 (KS.W30.RationalDivision.inputBits (a * b) c).length +
  ((4 * KS.W01.ratLength x + 2 * KS.W01.ratLength (a * b / c) + 4) +
    KS.W29.polynomialFuel 600000 3
      (KS.W01.encodeRat x ++ KS.W01.encodeRat (a * b / c)).length))))

theorem prepare_product_spec (x a b c : List Bool) :
    RunSpec (preparePair 20 21) (workspace [] [] x a b c)
      (workspace (a ++ b) [] x [] [] c) (4 * a.length + 2 * b.length + 4) := by
  have h := preparePair_spec 20 21 (by decide) (by decide) (by decide) (by decide)
    (workspace [] [] x a b c) rfl
  have he : pairAfter 20 21 (workspace [] [] x a b c) = workspace (a ++ b) [] x [] [] c := by
    funext j; fin_cases j <;> simp [pairAfter, WireAppend.after, workspace]
  rw [he] at h
  exact h

theorem prepare_division_spec (x p c : List Bool) :
    RunSpec (preparePair 10 22) (workspace [] p x [] [] c)
      (workspace (p ++ c) [] x [] [] []) (4 * p.length + 2 * c.length + 4) := by
  have h := preparePair_spec 10 22 (by decide) (by decide) (by decide) (by decide)
    (workspace [] p x [] [] c) rfl
  have he : pairAfter 10 22 (workspace [] p x [] [] c) = workspace (p ++ c) [] x [] [] [] := by
    funext j; fin_cases j <;> simp [pairAfter, WireAppend.after, workspace]
  rw [he] at h
  exact h

theorem prepare_subtraction_spec (x q : List Bool) :
    RunSpec (preparePair 19 10) (workspace [] q x [] [] [])
      (workspace (x ++ q) [] [] [] [] []) (4 * x.length + 2 * q.length + 4) := by
  have h := preparePair_spec 19 10 (by decide) (by decide) (by decide) (by decide)
    (workspace [] q x [] [] []) rfl
  have he : pairAfter 19 10 (workspace [] q x [] [] []) = workspace (x ++ q) [] [] [] [] [] := by
    funext j; fin_cases j <;> simp [pairAfter, WireAppend.after, workspace]
  rw [he] at h
  exact h

theorem multiply_spec (x a b c : ℚ) :
    RunSpec multiply
      (workspace (KS.W01.encodeRat a ++ KS.W01.encodeRat b) [] (KS.W01.encodeRat x) [] []
        (KS.W01.encodeRat c))
      (workspace [] (KS.W01.encodeRat (a * b)) (KS.W01.encodeRat x) [] []
        (KS.W01.encodeRat c)) (KS.W15.RationalMultiply.totalTicks a b) := by
  have h := first_spec (by decide : 13 ≤ 23) _ _ _
    (workspace [] [] (KS.W01.encodeRat x) [] [] (KS.W01.encodeRat c)) _
    (KS.W15.RationalMultiply.full_spec a b)
  have hb : extend (KS.W06.RationalCompare.fields
      (KS.W15.RationalMultiply.inputBits a b) [] [] [] [] [] [])
      (workspace [] [] (KS.W01.encodeRat x) [] [] (KS.W01.encodeRat c)) =
      workspace (KS.W01.encodeRat a ++ KS.W01.encodeRat b) [] (KS.W01.encodeRat x) [] []
        (KS.W01.encodeRat c) := by
    funext j; fin_cases j <;> rfl
  have ha : extend (KS.W01.SignedRationalSerializer.outputState (KS.W01.encodeRat (a*b)))
      (workspace [] [] (KS.W01.encodeRat x) [] [] (KS.W01.encodeRat c)) =
      workspace [] (KS.W01.encodeRat (a*b)) (KS.W01.encodeRat x) [] [] (KS.W01.encodeRat c) := by
    funext j; fin_cases j <;> rfl
  rw [hb, ha] at h
  exact h

theorem divide_spec (x p c : ℚ) :
    RunSpec divide
      (workspace (KS.W01.encodeRat p ++ KS.W01.encodeRat c) [] (KS.W01.encodeRat x) [] [] [])
      (workspace [] (KS.W01.encodeRat (p / c)) (KS.W01.encodeRat x) [] [] [])
      (KS.W29.polynomialFuel 1100000 3 (KS.W30.RationalDivision.inputBits p c).length) := by
  have h := first_spec (by decide : 15 ≤ 23) _ _ _
    (workspace [] [] (KS.W01.encodeRat x) [] [] []) _
    (KS.W30.RationalDivision.program_spec p c)
  have hb : extend (KS.W30.RationalDivision.inputState (KS.W30.RationalDivision.inputBits p c))
      (workspace [] [] (KS.W01.encodeRat x) [] [] []) =
      workspace (KS.W01.encodeRat p ++ KS.W01.encodeRat c) [] (KS.W01.encodeRat x) [] [] [] := by
    funext j; fin_cases j <;> rfl
  have ha : extend (KS.W30.RationalDivision.outputState (KS.W01.encodeRat (p/c)))
      (workspace [] [] (KS.W01.encodeRat x) [] [] []) =
      workspace [] (KS.W01.encodeRat (p/c)) (KS.W01.encodeRat x) [] [] [] := by
    funext j; fin_cases j <;> rfl
  rw [hb, ha] at h
  exact h

theorem subtract_spec (x q : ℚ) :
    RunSpec subtract (workspace (KS.W01.encodeRat x ++ KS.W01.encodeRat q) [] [] [] [] [])
      (workspace [] (KS.W01.encodeRat (x-q)) [] [] [] [])
      (KS.W29.polynomialFuel 600000 3 (KS.W01.encodeRat x ++ KS.W01.encodeRat q).length) := by
  have h := first_spec (by decide : 19 ≤ 23) _ _ _ (workspace [] [] [] [] [] []) _
    (KS.W13.RationalSubtract.polynomial_spec x q)
  have hb : extend (KS.W13.RationalSubtract.inputState (KS.W01.encodeRat x ++ KS.W01.encodeRat q))
      (workspace [] [] [] [] [] []) = workspace (KS.W01.encodeRat x ++ KS.W01.encodeRat q) [] [] [] [] [] := by
    funext j; fin_cases j <;> rfl
  have ha : extend (KS.W13.RationalSubtract.outputState (KS.W01.encodeRat (x-q)))
      (workspace [] [] [] [] [] []) = workspace [] (KS.W01.encodeRat (x-q)) [] [] [] [] := by
    funext j; fin_cases j <;> rfl
  rw [hb, ha] at h
  exact h

theorem full_spec (x a b c : ℚ) :
    RunSpec program
      (workspace [] [] (KS.W01.encodeRat x) (KS.W01.encodeRat a)
        (KS.W01.encodeRat b) (KS.W01.encodeRat c))
      (workspace [] (KS.W01.encodeRat (x - a * b / c)) [] [] [] []) (ticks x a b c) := by
  exact (prepare_product_spec _ _ _ _).compose ((multiply_spec x a b c).compose
    ((prepare_division_spec _ _ _).compose ((divide_spec x (a*b) c).compose
      ((prepare_subtraction_spec _ _).compose (subtract_spec x (a*b/c))))))

end KS.W07.SchurCellMachine

end

end OAI
