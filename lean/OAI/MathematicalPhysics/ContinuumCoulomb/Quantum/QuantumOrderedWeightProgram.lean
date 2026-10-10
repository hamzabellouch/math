import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedXZPipeline
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathScaleProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawFamilyProgram

namespace OAI

/-! Uniform literal rational-list programs for all five early gadget stages.
The lists retain input order and emit each fixed block in its word order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedWeightProgram
open ExactQuantumFactoring.BitStackProgram
open scoped BigOperators Classical

abbrev Pair := ℚ × ℚ
def pairCode : Pair → List Bool := prodCode ratCode ratCode
noncomputable opaque radius : Procedure pairCode ratCode Prod.fst := Procedure.first _ _
noncomputable opaque coupling : Procedure pairCode ratCode Prod.snd := Procedure.second _ _
noncomputable opaque radiusSquare : Procedure pairCode ratCode (fun x => x.1^2) :=
  QuantumRoutingCode.squareProgram radius
noncomputable opaque radiusCube : Procedure pairCode ratCode (fun x => x.1^3) :=
  (Procedure.ratMul.comp (radiusSquare.pair radius)).congrFun (by intro x; dsimp; ring)
noncomputable opaque radiusHalf : Procedure pairCode ratCode (fun x => x.1^2/2) :=
  Procedure.ratDiv.comp (radiusSquare.pair (Procedure.constant pairCode ratCode 2))
noncomputable opaque cubeHalf : Procedure pairCode ratCode (fun x => x.1^3/2) :=
  Procedure.ratDiv.comp (radiusCube.pair (Procedure.constant pairCode ratCode 2))
noncomputable opaque couplingHalf : Procedure pairCode ratCode (fun x => x.2/2) :=
  Procedure.ratDiv.comp (coupling.pair (Procedure.constant pairCode ratCode 2))
noncomputable opaque correction : Procedure pairCode ratCode (fun x => 1+(x.2/2)^2) :=
  Procedure.ratAdd.comp ((Procedure.constant pairCode ratCode 1).pair
    (QuantumRoutingCode.squareProgram couplingHalf))

noncomputable opaque fourProgram (k : Fin 4) : Procedure pairCode ratCode
    (fun x => QuantumPolarizedSubdivision.weight x.1 x.2 k) := by
  refine Fin.cases ?_ (fun k => ?_) k
  · exact (Procedure.ratAdd.comp (radiusHalf.pair correction)).congrFun
      (by intro x; change x.1^2/2+(1+(x.2/2)^2) = x.1^2/2+1+(x.2/2)^2; ring)
  · refine Fin.cases ?_ (fun k => ?_) k
    · exact (Procedure.ratNeg.comp radiusHalf).congrFun (by
        intro x; change -(x.1^2/2) = -x.1^2/2; ring)
    · refine Fin.cases ?_ (fun k => ?_) k
      · exact radius.congrFun (by intro x; rfl)
      · refine Fin.cases ?_ (fun k => Fin.elim0 k) k
        exact (Procedure.ratDiv.comp ((Procedure.ratMul.comp
          ((Procedure.ratNeg.comp radius).pair coupling)).pair
            (Procedure.constant pairCode ratCode 2))).congrFun (by intro x; rfl)

noncomputable opaque sevenProgram (k : Fin 7) : Procedure pairCode ratCode
    (fun x => QuantumPolarizedThird.weight x.1 x.2 k) := by
  refine Fin.cases ?_ (fun k => ?_) k
  · exact (Procedure.ratAdd.comp (cubeHalf.pair
      (Procedure.ratMul.comp (radius.pair correction)))).congrFun (by intro x; rfl)
  · refine Fin.cases ?_ (fun k => ?_) k
    · exact (Procedure.ratNeg.comp cubeHalf).congrFun (by
        intro x; change -(x.1^3/2) = -x.1^3/2; ring)
    · refine Fin.cases ?_ (fun k => ?_) k
      · exact (Procedure.ratMul.comp (radius.pair coupling)).congrFun (by intro x; rfl)
      · refine Fin.cases ?_ (fun k => ?_) k
        · exact (Procedure.ratSub.comp (radiusHalf.pair correction)).congrFun (by intro x; rfl)
        · refine Fin.cases ?_ (fun k => ?_) k
          · exact (Procedure.ratNeg.comp radiusHalf).congrFun (by
              intro x; change -(x.1^2/2) = -x.1^2/2; ring)
          · refine Fin.cases ?_ (fun k => ?_) k
            · exact radiusSquare.congrFun (by intro x; rfl)
            · refine Fin.cases ?_ (fun k => Fin.elim0 k) k
              exact (Procedure.ratDiv.comp ((Procedure.ratMul.comp (radiusSquare.pair coupling)).pair
                (Procedure.constant pairCode ratCode 2))).congrFun (by intro x; rfl)

abbrev Input := ℕ × List ℚ
def inputCode : Input → List Bool := prodCode unaryCode (listCode ratCode)
def scale (x : Input) : ℚ := 8*(4*(1+(x.2.map (fun j => (1+|j|)^2)).sum))^4*x.1

noncomputable opaque scaleProgram : Procedure inputCode ratCode scale := by
  let n := Procedure.natToRat.comp (Procedure.unaryToBits.comp
    (Procedure.first unaryCode (listCode ratCode)))
  let s := (QuantumPathScaleProgram.sumMapProgram QuantumPathScaleProgram.squareProgram).comp
    (Procedure.second unaryCode (listCode ratCode))
  let b := Procedure.ratMul.comp ((Procedure.constant inputCode ratCode 4).pair
    (Procedure.ratAdd.comp ((Procedure.constant inputCode ratCode 1).pair s)))
  let fourth := QuantumRoutingCode.squareProgram (QuantumRoutingCode.squareProgram b)
  exact (Procedure.ratMul.comp ((Procedure.ratMul.comp
    ((Procedure.constant inputCode ratCode 8).pair fourth)).pair n)).congrFun (by
      intro x
      simp only [Function.comp_apply,id_eq,scale,
        show QuantumPathScaleProgram.squareCost = (fun j : ℚ => (1+|j|)^2) from rfl]
      ring)

def block (d : ℕ) (f : Pair → Fin d → ℚ) (x : Pair) : List ℚ := List.ofFn (f x)
def stage (d : ℕ) (f : Pair → Fin d → ℚ) (x : Input) : List ℚ :=
  (x.2.map (fun j => block d f (scale x,j))).flatten

noncomputable def stageProgram (d : ℕ) (f : Pair → Fin d → ℚ)
    (p : ∀ k, Procedure pairCode ratCode (fun x => f x k)) :
    Procedure inputCode (listCode ratCode) (stage d f) := by
  let b : Procedure pairCode (listCode ratCode) (block d f) :=
    QuantumRawExchange.fixedListProgram pairCode ratCode d (fun k x => f x k) p
  let tab := Procedure.listMapWith (ea := ratCode) (eb := ratCode)
    (ec := listCode ratCode) (f := fun r j => block d f (r,j)) 0 [] b
  let env := scaleProgram.pair (Procedure.second unaryCode (listCode ratCode))
  exact (QuantumRawExchange.flattenProgram ratCode 0).comp (tab.comp env)

def four (x : Input) : List ℚ := stage 4
  (fun x => QuantumPolarizedSubdivision.weight x.1 x.2) x
def seven (x : Input) : List ℚ := stage 7
  (fun x => QuantumPolarizedThird.weight x.1 x.2) x
noncomputable opaque fourListProgram : Procedure inputCode (listCode ratCode) four :=
  stageProgram 4 _ fourProgram
noncomputable opaque sevenListProgram : Procedure inputCode (listCode ratCode) seven :=
  stageProgram 7 _ sevenProgram

def nextFour (x : Input) : Input := (x.1,four x)
def nextSeven (x : Input) : Input := (x.1,seven x)
noncomputable opaque nextFourProgram : Procedure inputCode inputCode nextFour :=
  (Procedure.first unaryCode (listCode ratCode)).pair fourListProgram
noncomputable opaque nextSevenProgram : Procedure inputCode inputCode nextSeven :=
  (Procedure.first unaryCode (listCode ratCode)).pair sevenListProgram

def output (x : Input) : List ℚ := seven (nextFour (nextSeven (nextFour (nextFour x))))
noncomputable opaque outputProgram : Procedure inputCode (listCode ratCode) output :=
  sevenListProgram.comp (nextFourProgram.comp (nextSevenProgram.comp
    (nextFourProgram.comp nextFourProgram)))

noncomputable def certificate :
    Turing.TM2ComputableInPolyTime inputCode (listCode ratCode) output := outputProgram.toTM2

theorem scale_ofFn {n : ℕ} (J : Fin n → ℚ) (N : ℕ) :
    scale (N,List.ofFn J) = QuantumOrderedSubdivision.scale J N := by
  simp only [scale,List.map_ofFn,List.sum_ofFn,Function.comp_apply,
    QuantumOrderedSubdivision.scale,QuantumOrderedSubdivision.budget]

theorem four_ofFn {n : ℕ} (J : Fin n → ℚ) (N : ℕ) :
    four (N,List.ofFn J) =
      (List.ofFn (fun i : Fin n => List.ofFn (fun k : Fin 4 =>
        QuantumOrderedSubdivision.outputCoefficient J N (i,k)))).flatten := by
  unfold four stage
  rw [scale_ofFn]
  simp only [List.map_ofFn,Function.comp_def,block,
    QuantumOrderedSubdivision.outputCoefficient]

theorem seven_ofFn {n : ℕ} (J : Fin n → ℚ) (N : ℕ) :
    seven (N,List.ofFn J) =
      (List.ofFn (fun i : Fin n => List.ofFn (fun k : Fin 7 =>
        QuantumOrderedThird.outputCoefficient J N (i,k)))).flatten := by
  unfold seven stage
  rw [scale_ofFn]
  simp only [List.map_ofFn,Function.comp_def,block,
    QuantumOrderedThird.outputCoefficient]

theorem stage_length (d : ℕ) (f : Pair → Fin d → ℚ) (x : Input) :
    (stage d f x).length = x.2.length*d := by
  have h (r : ℚ) (ys : List ℚ) :
      ((ys.map (fun j => block d f (r,j))).flatten).length = ys.length*d := by
    induction ys with
    | nil => simp
    | cons j js ih =>
      rw [List.map_cons,List.flatten_cons,List.length_append,ih]
      simp only [block,List.length_ofFn,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  exact h _ _

theorem output_length (x : Input) : (output x).length = 3136*x.2.length := by
  simp only [output,nextFour,nextSeven,four,seven,stage_length]
  omega

end ContinuumCoulomb.QuantumOrderedWeightProgram

end

end OAI
