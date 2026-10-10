import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.BisectionRegisters
import OAI.Computability.QuantumFactoring.BitStackProcedures

namespace OAI

/-! Literal polynomial-time bisection with a supplied polynomial-time
rational evaluator.  The evaluator environment and tolerance remain in
the input registers; they are not fixed nonuniform advice. -/

namespace ContinuumCoulomb.BisectionProgram
open ExactQuantumFactoring.BitStackProgram
open BisectionRegisters

abbrev Config (E : Type) := E × (ℚ × Registers)

def configCode {E : Type} (ce : E → List Bool) : Config E → List Bool :=
  prodCode ce (prodCode ratCode code)

def advance {E : Type} (evaluate : E → ℚ → ℚ) (s : Config E) : Config E :=
  (s.1, (s.2.1, step s.2.1 (evaluate s.1) s.2.2))

theorem iterate_config {E : Type} (evaluate : E → ℚ → ℚ) (s : Config E) (n : ℕ) :
    (advance evaluate)^[n] s =
      (s.1, (s.2.1, (step s.2.1 (evaluate s.1))^[n] s.2.2)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    rfl

theorem config_length {E : Type} (ce : E → List Bool) (s : Config E) :
    (configCode ce s).length =
      2 * (ce s.1).length + 2 * (ratCode s.2.1).length + (code s.2.2).length + 2 := by
  simp only [configCode, prodCode, pairBits_length]
  omega

theorem iterate_code_bound {E : Type} (ce : E → List Bool) (evaluate : E → ℚ → ℚ)
    (n : ℕ) (s : Config E) (i : ℕ) (hi : i ≤ n) :
    (configCode ce ((advance evaluate)^[i] s)).length ≤
      (8 * (Polynomial.X + 1) ^ 2 + 20 : Polynomial ℕ).eval
        (n + (configCode ce s).length) := by
  rw [iterate_config, config_length]
  have hb := iterate_bits s.2.1 (evaluate s.1) s.2.2 i
  have hc := code_le_bits ((step s.2.1 (evaluate s.1))^[i] s.2.2)
  have hs := bits_le_code s.2.2
  have hlen := config_length ce s
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  nlinarith

noncomputable def rationalLess : Procedure (prodCode ratCode ratCode)
    Procedure.boolCode (fun q => decide (q.1 < q.2)) := by
  -- `q₁ < q₂` is the negative sign of `q₁-q₂`.
  let sub' := Procedure.ratSub
  exact (Procedure.intSign.comp (Procedure.ratNum.comp sub')).congrFun (by
    intro q
    simp only [Function.comp_apply, Rat.num_neg, sub_neg])

noncomputable def middleProgram : Procedure code ratCode middle := by
  let lo := Procedure.first intCode (prodCode intCode (prodCode Nat.bits Procedure.boolCode))
  let tail := Procedure.second intCode (prodCode intCode (prodCode Nat.bits Procedure.boolCode))
  let hi := (Procedure.first intCode (prodCode Nat.bits Procedure.boolCode)).comp tail
  let db := (Procedure.second intCode (prodCode Nat.bits Procedure.boolCode)).comp tail
  let den := (Procedure.first Nat.bits Procedure.boolCode).comp db
  exact (Procedure.makeRat.comp ((Procedure.intAdd.comp (lo.pair hi)).pair
    (Procedure.double.comp den))).congrFun (by intro s; rfl)

noncomputable def advanceProgram {E : Type} {ce : E → List Bool}
    {evaluate : E → ℚ → ℚ}
    (evalProgram : Procedure (prodCode ce ratCode) ratCode (fun x => evaluate x.1 x.2)) :
    Procedure (configCode ce) (configCode ce) (advance evaluate) := by
  let env := Procedure.first ce (prodCode ratCode code)
  let tail := Procedure.second ce (prodCode ratCode code)
  let tolerance := (Procedure.first ratCode code).comp tail
  let regs := (Procedure.second ratCode code).comp tail
  let lo := (Procedure.first intCode (prodCode intCode (prodCode Nat.bits Procedure.boolCode))).comp regs
  let rest := (Procedure.second intCode (prodCode intCode (prodCode Nat.bits Procedure.boolCode))).comp regs
  let hi := (Procedure.first intCode (prodCode Nat.bits Procedure.boolCode)).comp rest
  let db := (Procedure.second intCode (prodCode Nat.bits Procedure.boolCode)).comp rest
  let den := (Procedure.first Nat.bits Procedure.boolCode).comp db
  let settled := (Procedure.second Nat.bits Procedure.boolCode).comp db
  let sum := Procedure.intAdd.comp (lo.pair hi)
  let two := Procedure.constant (configCode ce) intCode (2 : ℤ)
  let twiceLo := Procedure.intMul.comp (two.pair lo)
  let twiceHi := Procedure.intMul.comp (two.pair hi)
  let twiceDen := Procedure.double.comp den
  let no := Procedure.constant (configCode ce) Procedure.boolCode false
  let yes := Procedure.constant (configCode ce) Procedure.boolCode true
  let leftRegs := sum.pair (twiceHi.pair (twiceDen.pair no))
  let rightRegs := twiceLo.pair (sum.pair (twiceDen.pair no))
  let stoppedRegs := sum.pair (sum.pair (twiceDen.pair yes))
  let middle := middleProgram.comp regs
  let value := evalProgram.comp (env.pair middle)
  let positive := rationalLess.comp (tolerance.pair value)
  let negative := rationalLess.comp (value.pair (Procedure.ratNeg.comp tolerance))
  let moved := Procedure.conditional positive leftRegs
    (Procedure.conditional negative rightRegs stoppedRegs)
  let result := Procedure.conditional settled regs moved
  exact (env.pair (tolerance.pair result)).congrFun (by
    intro s
    simp only [advance, step, Function.comp_apply, decide_eq_true_eq])

noncomputable def repeatProgram {E : Type} {ce : E → List Bool}
    {evaluate : E → ℚ → ℚ}
    (evalProgram : Procedure (prodCode ce ratCode) ratCode (fun x => evaluate x.1 x.2)) :
    Procedure (prodCode (fun n => List.replicate n true) (configCode ce)) (configCode ce)
      (fun x => (advance evaluate)^[x.1] x.2) :=
  (advanceProgram evalProgram).iterate (8 * (Polynomial.X + 1) ^ 2 + 20)
    (iterate_code_bound ce evaluate)

noncomputable def initialProgram : Procedure (prodCode ratCode ratCode) code
    (fun p => initial p.1 p.2) := by
  let a := Procedure.first ratCode ratCode
  let b := Procedure.second ratCode ratCode
  let an := Procedure.ratNum.comp a
  let bn := Procedure.ratNum.comp b
  let ad := Procedure.ratDen.comp a
  let bd := Procedure.ratDen.comp b
  let lo := Procedure.intMul.comp (an.pair (Procedure.natToInt.comp bd))
  let hi := Procedure.intMul.comp (bn.pair (Procedure.natToInt.comp ad))
  let den := Procedure.binaryMul.comp (ad.pair bd)
  exact (lo.pair (hi.pair (den.pair
    (Procedure.constant (prodCode ratCode ratCode) Procedure.boolCode false)))).congrFun
      (by intro p; rfl)

abbrev Input (E : Type) := ℕ × (E × (ℚ × (ℚ × ℚ)))

def inputCode {E : Type} (ce : E → List Bool) : Input E → List Bool :=
  prodCode (fun n => List.replicate n true)
    (prodCode ce (prodCode ratCode (prodCode ratCode ratCode)))

def approximate {E : Type} (evaluate : E → ℚ → ℚ) (x : Input E) : ℚ :=
  middle ((step x.2.2.1 (evaluate x.2.1))^[x.1] (initial x.2.2.2.1 x.2.2.2.2))

noncomputable def program {E : Type} {ce : E → List Bool}
    {evaluate : E → ℚ → ℚ}
    (evalProgram : Procedure (prodCode ce ratCode) ratCode (fun x => evaluate x.1 x.2)) :
    Procedure (inputCode ce) ratCode (approximate evaluate) := by
  let n := Procedure.first (fun n => List.replicate n true)
    (prodCode ce (prodCode ratCode (prodCode ratCode ratCode)))
  let tail := Procedure.second (fun n => List.replicate n true)
    (prodCode ce (prodCode ratCode (prodCode ratCode ratCode)))
  let env := (Procedure.first ce (prodCode ratCode (prodCode ratCode ratCode))).comp tail
  let rest := (Procedure.second ce (prodCode ratCode (prodCode ratCode ratCode))).comp tail
  let tolerance := (Procedure.first ratCode (prodCode ratCode ratCode)).comp rest
  let endpoints := (Procedure.second ratCode (prodCode ratCode ratCode)).comp rest
  let config := env.pair (tolerance.pair (initialProgram.comp endpoints))
  let run := (repeatProgram evalProgram).comp (n.pair config)
  let extract := (Procedure.second ratCode code).comp (Procedure.second ce (prodCode ratCode code))
  exact (middleProgram.comp (extract.comp run)).congrFun (by
    intro x
    simp only [Function.comp_apply, iterate_config, approximate])

noncomputable def certificate {E : Type} {ce : E → List Bool}
    {evaluate : E → ℚ → ℚ}
    (evalProgram : Procedure (prodCode ce ratCode) ratCode (fun x => evaluate x.1 x.2)) :
    Turing.TM2ComputableInPolyTime (inputCode ce) ratCode (approximate evaluate) :=
  (program evalProgram).toTM2

theorem residual {E : Type} (evaluate : E → ℚ → ℚ) (e : E)
    {a b δ : ℚ} {f : ℝ → ℝ} {L : ℝ}
    (hδ : 0 ≤ δ) (hab : a ≤ b) (ha : 0 ≤ f a) (hb : f b ≤ 0) (hL : 0 ≤ L)
    (heval : ∀ q ∈ Set.Icc a b, |(evaluate e q : ℝ) - f q| ≤ (δ : ℝ))
    (hLip : ∀ x ∈ Set.Icc (a : ℝ) b, ∀ y ∈ Set.Icc (a : ℝ) b,
      |f x - f y| ≤ L * |x - y|) (n : ℕ) :
    |f (approximate evaluate (n, (e, (δ, (a, b)))))| ≤
      2 * (δ : ℝ) + L * (((b : ℝ) - a) / 2 ^ n) :=
  BisectionRegisters.residual hδ hab ha hb hL heval hLip n

end ContinuumCoulomb.BisectionProgram

end OAI
