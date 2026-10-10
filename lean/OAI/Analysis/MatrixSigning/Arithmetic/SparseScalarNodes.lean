import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalDivisionMachine
import OAI.Analysis.MatrixSigning.Complexity.ComplexScalarCosts

namespace OAI

section

namespace KS.W19.SparseScalarNodes
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W15.ComplexMachine

def divPorts : Fin 15 ↪ Fin 28 := Fin.castLEEmb (by decide)
def divProgram : Program 28 := liftPorts KS.W30.RationalDivision.program divPorts

def divTicks (q r : ℚ) : ℕ := KS.W29.polynomialFuel 1100000 3
  (KS.W30.RationalDivision.inputBits q r).length

theorem scalar_division_spec (before : Registers) (hclear : CoreEmpty before) (q r : ℚ) :
    RunSpec divProgram (Function.update before 0 (KS.W01.encodeRat q ++ KS.W01.encodeRat r))
      (Function.update before 10 (KS.W01.encodeRat (q/r))) (divTicks q r) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ divPorts _ _ _ _ _
    (KS.W30.RationalDivision.program_spec q r)
  · intro i; fin_cases i <;> simp [divPorts,KS.W30.RationalDivision.inputState,
      KS.W30.RationalDivision.inputBits,Function.update,coreEmpty_apply before hclear] <;> rfl
  · intro i; fin_cases i <;> simp [divPorts,KS.W30.RationalDivision.outputState,
      Function.update,coreEmpty_apply before hclear] <;> rfl
  · intro j hj
    have h0 : j ≠ 0 := hj 0
    have h10 : j ≠ 10 := hj 10
    simp [Function.update,h0,h10]

def divNode (a b dest : Fin 28) (ha : 16 ≤ a.val) (hb : 16 ≤ b.val) : Program 28 :=
  compose (compose (pairProgram a b ha hb) divProgram) (storeProgram dest)
def divNodeTicks (q r : ℚ) : ℕ := pairTicks (KS.W01.encodeRat q) (KS.W01.encodeRat r) +
  divTicks q r + (2*(KS.W01.encodeRat (q/r)).length+2)

theorem divNode_spec (a b dest : Fin 28) (ha : 16 ≤ a.val) (hb : 16 ≤ b.val)
    (hd : 16 ≤ dest.val) (before : Registers) (hclear : CoreEmpty before)
    (q r : ℚ) (hq : before a = KS.W01.encodeRat q) (hr : before b = KS.W01.encodeRat r)
    (hempty : before dest = []) :
    RunSpec (divNode a b dest ha hb) before
      (Function.update before dest (KS.W01.encodeRat (q/r))) (divNodeTicks q r) := by
  have hp := pair_spec a b ha hb before hclear
  rw [hq,hr] at hp
  exact (hp.compose (scalar_division_spec before hclear q r)).compose
    (store_spec before hclear dest hd hempty _)

def coefficient (a b : ℚ) : ℚ := -(a+1)/(2*b)
def put (s : Registers) (p : Fin 28) (q : ℚ) : Registers := Function.update s p (KS.W01.encodeRat q)
def after (s : Registers) (a b : ℚ) : Registers :=
  put (put (put (put (put (put s 20 1) 21 2) 18 (a+1)) 19 (2*b)) 24 (-(a+1))) 25 (coefficient a b)

def program : Program 28 := compose (KS.W15.WireProgram.literalProgram 20 (KS.W01.encodeRat 1))
  (compose (KS.W15.WireProgram.literalProgram 21 (KS.W01.encodeRat 2))
    (compose (addNode 16 20 18 (by decide) (by decide))
      (compose (mulNode 21 17 19 (by decide) (by decide))
        (compose (negNode 18 24 (by decide)) (divNode 24 19 25 (by decide) (by decide))))))
def ticks (a b : ℚ) : ℕ := (KS.W01.encodeRat 1).length+1 +
  ((KS.W01.encodeRat 2).length+1 + (addNodeTicks a 1 +
    (mulNodeTicks 2 b + (negNodeTicks (a+1) + divNodeTicks (-(a+1)) (2*b)))))

theorem coefficient_spec (s : Registers) (a b : ℚ) (hc : CoreEmpty s)
    (ha : s 16 = KS.W01.encodeRat a) (hb : s 17 = KS.W01.encodeRat b)
    (h18 : s 18 = []) (h19 : s 19 = []) (h20 : s 20 = []) (h21 : s 21 = [])
    (h24 : s 24 = []) (h25 : s 25 = []) :
    RunSpec program s (after s a b) (ticks a b) := by
  let s1 := put s 20 1
  let s2 := put s1 21 2
  let s3 := put s2 18 (a+1)
  let s4 := put s3 19 (2*b)
  let s5 := put s4 24 (-(a+1))
  have h1 : RunSpec (KS.W15.WireProgram.literalProgram 20 (KS.W01.encodeRat 1)) s s1
      ((KS.W01.encodeRat 1).length+1) := by
    simpa [s1,put,h20] using KS.W15.WireProgram.literal_spec (20 : Fin 28) (KS.W01.encodeRat 1) s
  have h2 : RunSpec (KS.W15.WireProgram.literalProgram 21 (KS.W01.encodeRat 2)) s1 s2
      ((KS.W01.encodeRat 2).length+1) := by
    simpa [s2,s1,put,h21] using KS.W15.WireProgram.literal_spec (21 : Fin 28) (KS.W01.encodeRat 2) s1
  have hc1 : CoreEmpty s1 := coreEmpty_update s hc 20 (by decide) _
  have hc2 : CoreEmpty s2 := coreEmpty_update s1 hc1 21 (by decide) _
  have h3 : RunSpec (addNode 16 20 18 (by decide) (by decide)) s2 s3 (addNodeTicks a 1) := by
    apply addNode_spec 16 20 18 (by decide) (by decide) (by decide) s2 hc2 a 1
    · simp [s2,s1,put,ha]
    · simp [s2,s1,put]
    · simp [s2,s1,put,h18]
  have hc3 : CoreEmpty s3 := coreEmpty_update s2 hc2 18 (by decide) _
  have h4 : RunSpec (mulNode 21 17 19 (by decide) (by decide)) s3 s4 (mulNodeTicks 2 b) := by
    apply mulNode_spec 21 17 19 (by decide) (by decide) (by decide) s3 hc3 2 b
    · simp [s3,s2,s1,put]
    · simp [s3,s2,s1,put,hb]
    · simp [s3,s2,s1,put,h19]
  have hc4 : CoreEmpty s4 := coreEmpty_update s3 hc3 19 (by decide) _
  have h5 : RunSpec (negNode 18 24 (by decide)) s4 s5 (negNodeTicks (a+1)) := by
    apply negNode_spec 18 24 (by decide) (by decide) s4 hc4 (a+1)
    · simp [s4,s3,put]
    · simp [s4,s3,s2,s1,put,h24]
  have hc5 : CoreEmpty s5 := coreEmpty_update s4 hc4 24 (by decide) _
  have h6 : RunSpec (divNode 24 19 25 (by decide) (by decide)) s5 (after s a b)
      (divNodeTicks (-(a+1)) (2*b)) := by
    apply divNode_spec 24 19 25 (by decide) (by decide) (by decide) s5 hc5 (-(a+1)) (2*b)
    · simp [s5,put]
    · simp [s5,s4,put]
    · simp [s5,s4,s3,s2,s1,put,h25]
  exact h1.compose (h2.compose (h3.compose (h4.compose (h5.compose h6))))

end KS.W19.SparseScalarNodes

end

end OAI
