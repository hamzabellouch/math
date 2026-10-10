import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.UniformSamples
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.RationalSumProgram
import OAI.Computability.QuantumFactoring.BitStackTabulate

namespace OAI

/-! Literal tabulation and summation of rational quadrature samples.
The sample count is unary; bounds, spacing and evaluator data are encoded
as ordinary inputs to the machine. -/

namespace ContinuumCoulomb.RationalQuadratureProgram
open ExactQuantumFactoring.BitStackProgram
open scoped BigOperators

variable {E : Type}

abbrev Environment (E : Type) := E × (ℚ × ℚ)
abbrev Input (E : Type) := ℕ × Environment E

def environmentCode (ce : E → List Bool) : Environment E → List Bool :=
  prodCode ce (prodCode ratCode ratCode)

def inputCode (ce : E → List Bool) : Input E → List Bool :=
  prodCode unaryCode (environmentCode ce)

def node (a h : ℚ) (i : ℕ) : ℚ := a + (i : ℚ) * h

def sample (evaluate : E → ℚ → ℚ) (e : Environment E) (i : ℕ) : ℚ :=
  evaluate e.1 (node e.2.1 e.2.2 i)

def value (evaluate : E → ℚ → ℚ) (x : Input E) : ℚ :=
  x.2.2.2 * ∑ i ∈ Finset.range x.1, sample evaluate x.2 i

theorem range_sum (f : ℕ → ℚ) (N : ℕ) :
    ((List.range N).map f).sum = ∑ i ∈ Finset.range N, f i := by
  induction N with
  | zero => simp
  | succ N ih => simp [List.range_succ, Finset.sum_range_succ, ih]

noncomputable def sampleProgram (ce : E → List Bool) (evaluate : E → ℚ → ℚ)
    (p : Procedure (prodCode ce ratCode) ratCode (fun x => evaluate x.1 x.2)) :
    Procedure (inputCode ce) ratCode (fun x => sample evaluate x.2 x.1) := by
  let i := Procedure.first unaryCode (environmentCode ce)
  let env := Procedure.second unaryCode (environmentCode ce)
  let e := (Procedure.first ce (prodCode ratCode ratCode)).comp env
  let ah := (Procedure.second ce (prodCode ratCode ratCode)).comp env
  let a := (Procedure.first ratCode ratCode).comp ah
  let h := (Procedure.second ratCode ratCode).comp ah
  let ir := Procedure.natToRat.comp (Procedure.unaryToBits.comp i)
  let t := Procedure.ratAdd.comp (a.pair (Procedure.ratMul.comp (ir.pair h)))
  exact (p.comp (e.pair t)).congrFun (by intro x; rfl)

noncomputable def program (ce : E → List Bool) (evaluate : E → ℚ → ℚ)
    (p : Procedure (prodCode ce ratCode) ratCode (fun x => evaluate x.1 x.2)) :
    Procedure (inputCode ce) ratCode (value evaluate) := by
  let samples := Procedure.tabulate (0 : ℚ) (sampleProgram ce evaluate p)
  let sum := RationalSumProgram.sumProgram.comp samples
  let env := Procedure.second unaryCode (environmentCode ce)
  let ah := (Procedure.second ce (prodCode ratCode ratCode)).comp env
  let h := (Procedure.second ratCode ratCode).comp ah
  exact (Procedure.ratMul.comp (h.pair sum)).congrFun (by
    intro x
    change x.2.2.2 * ((List.range x.1).map (sample evaluate x.2)).sum = value evaluate x
    rw [range_sum]
    rfl)

noncomputable def certificate (ce : E → List Bool) (evaluate : E → ℚ → ℚ)
    (p : Procedure (prodCode ce ratCode) ratCode (fun x => evaluate x.1 x.2)) :
    Turing.TM2ComputableInPolyTime (inputCode ce) ratCode (value evaluate) :=
  (program ce evaluate p).toTM2

theorem node_cast (a h : ℚ) (i : ℕ) :
    (node a h i : ℝ) = UniformQuadrature.node (a : ℝ) (h : ℝ) i := by
  simp [node, UniformQuadrature.node]

theorem value_cast (evaluate : E → ℚ → ℚ) (x : Input E) :
    (value evaluate x : ℝ) = UniformQuadrature.sampleSum (x.2.2.2 : ℝ) x.1
      (fun i => (sample evaluate x.2 i : ℝ)) := by
  simp [value, UniformQuadrature.sampleSum]

theorem error (evaluate : E → ℚ → ℚ) (x : Input E) (f : ℝ → ℝ) {L ε : ℝ}
    (hh : 0 ≤ (x.2.2.2 : ℝ)) (hL : 0 ≤ L) (hf : Continuous f)
    (hLip : ∀ u ∈ Set.Icc (x.2.2.1 : ℝ) (node x.2.2.1 x.2.2.2 x.1 : ℝ),
      ∀ v ∈ Set.Icc (x.2.2.1 : ℝ) (node x.2.2.1 x.2.2.2 x.1 : ℝ),
      |f u - f v| ≤ L * |u - v|)
    (heval : ∀ i < x.1, |(sample evaluate x.2 i : ℝ) -
      f (node x.2.2.1 x.2.2.2 i : ℝ)| ≤ ε) :
    |(value evaluate x : ℝ) - ∫ t in (x.2.2.1 : ℝ)..(node x.2.2.1 x.2.2.2 x.1 : ℝ), f t| ≤
      (x.1 : ℝ) * (L * (x.2.2.2 : ℝ) ^ 2 + (x.2.2.2 : ℝ) * ε) := by
  rw [value_cast, node_cast]
  apply UniformQuadrature.samples_error f _ _ _ _ hh hL hf
  · simpa only [node_cast] using hLip
  · simpa only [node_cast] using heval

end ContinuumCoulomb.RationalQuadratureProgram

end OAI
