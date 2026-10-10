import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalAddProgram
import OAI.Analysis.MatrixSigning.Arithmetic.RationalMultiplicationMachine
import OAI.Analysis.MatrixSigning.Encoding.WireProgramPrimitives

namespace OAI

namespace KS.W15.ComplexMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W15.WireProgram

abbrev Registers := Fin 28 → List Bool

def corePorts : Fin 16 ↪ Fin 28 :=
  ⟨fun i => ⟨i.val,by omega⟩,by intro i j h; exact Fin.ext (congrArg (fun p : Fin 28 => p.val) h)⟩
def mulPorts : Fin 13 ↪ Fin 28 :=
  ⟨fun i => ⟨i.val,by omega⟩,by intro i j h; exact Fin.ext (congrArg (fun p : Fin 28 => p.val) h)⟩

@[simp] private theorem corePorts_apply (i : Fin 16) :
    corePorts i = ⟨i.val, by omega⟩ := rfl

@[simp] private theorem mulPorts_apply (i : Fin 13) :
    mulPorts i = ⟨i.val, by omega⟩ := rfl

def CoreEmpty (s : Registers) : Prop := ∀ i : Fin 16, s (corePorts i) = []

theorem coreEmpty_apply (s : Registers) (h : CoreEmpty s) (j : Fin 28) (hj : j.val < 16) :
    s j = [] := by
  have he : corePorts ⟨j.val,hj⟩ = j := Fin.ext rfl
  simpa only [he] using h ⟨j.val,hj⟩

theorem stored_ne_core (a : Fin 28) (ha : 16 ≤ a.val) (i : Fin 16) : a ≠ corePorts i := by
  intro h
  have hv := congrArg Fin.val h
  change a.val = i.val at hv
  have hi := i.isLt
  omega

def pairProgram (a b : Fin 28) (ha : 16 ≤ a.val) (hb : 16 ≤ b.val) : Program 28 :=
  compose (compose
    (copyProgram b 0 1 (stored_ne_core b hb 0) (stored_ne_core b hb 1) (by decide))
    (copyProgram a 2 1 (stored_ne_core a ha 2) (stored_ne_core a ha 1) (by decide)))
      (transferProgram 2 0 1)

def pairTicks (x y : List Bool) : Nat := 4 * x.length + 2 * y.length + 6

theorem pair_spec (a b : Fin 28) (ha : 16 ≤ a.val) (hb : 16 ≤ b.val)
    (before : Registers) (hclear : CoreEmpty before) :
    RunSpec (pairProgram a b ha hb) before
      (Function.update before 0 (before a ++ before b)) (pairTicks (before a) (before b)) := by
  have h0 : before (0 : Fin 28) = [] := hclear 0
  have h1 : before (1 : Fin 28) = [] := hclear 1
  have h2 : before (2 : Fin 28) = [] := hclear 2
  have ha0 : a ≠ (0 : Fin 28) := stored_ne_core a ha 0
  let s1 := Function.update before (0 : Fin 28) (before b)
  let s2 := Function.update s1 (2 : Fin 28) (before a)
  have hc1 := copy_spec b (0 : Fin 28) 1 (stored_ne_core b hb 0) (stored_ne_core b hb 1)
    (by decide) before h0 h1
  have hc2 : RunSpec
      (copyProgram a (2 : Fin 28) 1 (stored_ne_core a ha 2) (stored_ne_core a ha 1) (by decide))
      s1 s2 (2 * (before a).length + 2) := by
    have h := copy_spec a (2 : Fin 28) 1 (stored_ne_core a ha 2) (stored_ne_core a ha 1)
      (by decide) s1 (by simpa [s1] using h2) (by simpa [s1] using h1)
    simpa [s1,s2,ha0] using h
  have ht := transfer_spec (2 : Fin 28) 0 1 (by decide) (by decide) (by decide) s2
    (by simpa [s1,s2] using h1)
  have h := (hc1.compose hc2).compose ht
  convert h using 1 <;> (try rfl)
  · funext j
    by_cases hj0 : j = 0 <;> by_cases hj1 : j = 1 <;> by_cases hj2 : j = 2 <;>
      simp_all [transferAfter,s1,s2,Function.update]
  · simp [pairTicks,s1,s2]
    omega

def mulProgram : Program 28 := KS.W29.FixedSequential.liftPorts RationalMultiply.program mulPorts
def addProgram : Program 28 := KS.W29.FixedSequential.liftPorts KS.W13.RationalAdd.program corePorts

def scalarAfter (before : Registers) (out : List Bool) : Registers :=
  Function.update (Function.update before 0 []) 10 out

theorem scalar_multiplication_spec (before : Registers) (hclear : CoreEmpty before) (q r : ℚ) :
    RunSpec mulProgram (Function.update before 0 (KS.W01.encodeRat q ++ KS.W01.encodeRat r))
      (Function.update before 10 (KS.W01.encodeRat (q * r))) (RationalMultiply.totalTicks q r) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ _ _ _ _ _ _ (RationalMultiply.full_spec q r)
  · intro i
    fin_cases i <;> simp [mulPorts_apply,KS.W06.RationalCompare.fields,RationalMultiply.inputBits,Function.update,
      coreEmpty_apply before hclear]
  · intro i
    fin_cases i <;> simp [mulPorts_apply,KS.W01.SignedRationalSerializer.outputState,Function.update,
      coreEmpty_apply before hclear]
  · intro j hj
    have hj0 : j ≠ 0 := hj 0
    have hj10 : j ≠ 10 := hj 10
    simp [Function.update,hj0,hj10]

theorem scalar_addition_spec (before : Registers) (hclear : CoreEmpty before) (q r : ℚ) :
    RunSpec addProgram (Function.update before 0 (KS.W01.encodeRat q ++ KS.W01.encodeRat r))
      (Function.update before 10 (KS.W01.encodeRat (q + r))) (KS.W13.RationalAdd.totalTicks q r) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ _ _ _ _ _ _ (KS.W13.RationalAdd.full_spec q r)
  · intro i
    fin_cases i <;> simp [corePorts_apply,KS.W13.RationalAdd.inputState,KS.W13.RationalAdd.extend,
      KS.W06.RationalCompare.fields,Function.update,
      coreEmpty_apply before hclear]
  · intro i
    fin_cases i <;> simp [corePorts_apply,KS.W13.RationalAdd.outputState,KS.W13.RationalAdd.extend,
      KS.W01.SignedRationalSerializer.outputState,Function.update,
      coreEmpty_apply before hclear]
  · intro j hj
    have hj0 : j ≠ 0 := hj 0
    have hj10 : j ≠ 10 := hj 10
    simp [Function.update,hj0,hj10]

def storeProgram (dest : Fin 28) : Program 28 := transferProgram 10 dest 1

theorem store_spec (before : Registers) (hclear : CoreEmpty before)
    (dest : Fin 28) (hd : 16 ≤ dest.val) (hempty : before dest = []) (wire : List Bool) :
    RunSpec (storeProgram dest) (Function.update before 10 wire)
      (Function.update before dest wire) (2 * wire.length + 2) := by
  have hd10 : dest ≠ (10 : Fin 28) := stored_ne_core dest hd 10
  have hd1 : dest ≠ (1 : Fin 28) := stored_ne_core dest hd 1
  have h10 : before (10 : Fin 28) = [] := hclear 10
  have h1 : before (1 : Fin 28) = [] := hclear 1
  have ht := transfer_spec (10 : Fin 28) dest 1 hd10.symm (by decide) hd1
    (Function.update before 10 wire) (by simpa using h1)
  convert ht using 1 <;> (try rfl)
  · funext j
    by_cases hj10 : j = 10 <;> by_cases hjd : j = dest <;>
      simp_all [transferAfter,Function.update]

def mulNode (a b dest : Fin 28) (ha : 16 ≤ a.val) (hb : 16 ≤ b.val) : Program 28 :=
  compose (compose (pairProgram a b ha hb) mulProgram) (storeProgram dest)
def addNode (a b dest : Fin 28) (ha : 16 ≤ a.val) (hb : 16 ≤ b.val) : Program 28 :=
  compose (compose (pairProgram a b ha hb) addProgram) (storeProgram dest)

def mulNodeTicks (q r : ℚ) : Nat :=
  pairTicks (KS.W01.encodeRat q) (KS.W01.encodeRat r) + RationalMultiply.totalTicks q r +
    (2 * (KS.W01.encodeRat (q * r)).length + 2)
def addNodeTicks (q r : ℚ) : Nat :=
  pairTicks (KS.W01.encodeRat q) (KS.W01.encodeRat r) + KS.W13.RationalAdd.totalTicks q r +
    (2 * (KS.W01.encodeRat (q + r)).length + 2)

theorem mulNode_spec (a b dest : Fin 28) (ha : 16 ≤ a.val) (hb : 16 ≤ b.val)
    (hd : 16 ≤ dest.val) (before : Registers) (hclear : CoreEmpty before)
    (q r : ℚ) (hq : before a = KS.W01.encodeRat q) (hr : before b = KS.W01.encodeRat r)
    (hempty : before dest = []) :
    RunSpec (mulNode a b dest ha hb) before
      (Function.update before dest (KS.W01.encodeRat (q * r))) (mulNodeTicks q r) := by
  have hp := pair_spec a b ha hb before hclear
  rw [hq,hr] at hp
  exact (hp.compose (scalar_multiplication_spec before hclear q r)).compose
    (store_spec before hclear dest hd hempty _)

theorem addNode_spec (a b dest : Fin 28) (ha : 16 ≤ a.val) (hb : 16 ≤ b.val)
    (hd : 16 ≤ dest.val) (before : Registers) (hclear : CoreEmpty before)
    (q r : ℚ) (hq : before a = KS.W01.encodeRat q) (hr : before b = KS.W01.encodeRat r)
    (hempty : before dest = []) :
    RunSpec (addNode a b dest ha hb) before
      (Function.update before dest (KS.W01.encodeRat (q + r))) (addNodeTicks q r) := by
  have hp := pair_spec a b ha hb before hclear
  rw [hq,hr] at hp
  exact (hp.compose (scalar_addition_spec before hclear q r)).compose
    (store_spec before hclear dest hd hempty _)

theorem coreEmpty_update (before : Registers) (hclear : CoreEmpty before)
    (dest : Fin 28) (hd : 16 ≤ dest.val) (wire : List Bool) :
    CoreEmpty (Function.update before dest wire) := by
  intro i
  rw [Function.update_of_ne (stored_ne_core dest hd i).symm]
  exact hclear i

end KS.W15.ComplexMachine

end OAI
