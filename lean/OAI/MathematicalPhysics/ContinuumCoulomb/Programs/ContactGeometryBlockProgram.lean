import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.ContactPlacedGadgetProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactMediator

namespace OAI

/-! Uniform polynomial-time serialization of the actual mediator vertex
blocks: old vertices, first sites, second sites, and the two third-site
blocks. The static local labels agree with `ContactMediator.encodeSite`. -/

noncomputable section
namespace ContinuumCoulomb.ContactGeometryBlockProgram
open ExactQuantumFactoring.BitStackProgram ContactMediator

abbrev EdgeInput := ContactPlacedGadgetProgram.Input

def defaultEdge : EdgeInput := (((0, 0), (1, 0)), (0, (false, (1, ([], [])))))

def pointCode : (ℚ × ℚ) → List Bool := ContactRationalGadget.pointCode

def block (ss : List ContactGadgetSite) (xs : List EdgeInput) : List (ℚ × ℚ) :=
  (List.range (ss.length * xs.length)).map fun i =>
    ((ss.map (ContactPlacedGadgetProgram.position
      ((xs.drop (i / ss.length)).headD defaultEdge))).drop (i % ss.length)).headD (0, 0)

abbrev LoopInput := ℕ × List EdgeInput

def loopCode : LoopInput → List Bool :=
  prodCode unaryCode (listCode ContactPlacedGadgetProgram.inputCode)

noncomputable opaque indexProgram : Procedure loopCode Nat.bits (fun x => x.1) :=
  Procedure.unaryToBits.comp (Procedure.first unaryCode _)

noncomputable opaque edgesProgram : Procedure loopCode
    (listCode ContactPlacedGadgetProgram.inputCode) Prod.snd := Procedure.second unaryCode _

noncomputable opaque quotientProgram (n : ℕ) : Procedure loopCode Nat.bits
    (fun x => x.1 / n) := Procedure.binaryDiv.comp
      (indexProgram.pair (Procedure.constant loopCode Nat.bits n))

noncomputable opaque remainderProgram (n : ℕ) : Procedure loopCode Nat.bits
    (fun x => x.1 % n) := Procedure.binaryMod.comp
      (indexProgram.pair (Procedure.constant loopCode Nat.bits n))

noncomputable opaque edgeProgram (n : ℕ) : Procedure loopCode ContactPlacedGadgetProgram.inputCode
    (fun x => (x.2.drop (x.1 / n)).headD defaultEdge) :=
  (Procedure.listGet ContactPlacedGadgetProgram.inputCode defaultEdge).comp
    ((quotientProgram n).pair edgesProgram)

noncomputable opaque pointListProgram (ss : List ContactGadgetSite) : Procedure loopCode
    (listCode pointCode) (fun x => ss.map (ContactPlacedGadgetProgram.position
      ((x.2.drop (x.1 / ss.length)).headD defaultEdge))) :=
  (ContactPlacedGadgetProgram.pointListProgram ss).comp (edgeProgram ss.length)

noncomputable opaque stepProgram (ss : List ContactGadgetSite) : Procedure loopCode pointCode
    (fun x => ((ss.map (ContactPlacedGadgetProgram.position
      ((x.2.drop (x.1 / ss.length)).headD defaultEdge))).drop (x.1 % ss.length)).headD (0, 0)) :=
  (Procedure.listGet pointCode (0, 0)).comp
    ((remainderProgram ss.length).pair (pointListProgram ss))

noncomputable opaque blockProgram (ss : List ContactGadgetSite) :
    Procedure (listCode ContactPlacedGadgetProgram.inputCode) (listCode pointCode) (block ss) := by
  let len := ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength
    ContactPlacedGadgetProgram.inputCode defaultEdge
  let count := (CoulombEvaluation.scaleProgram ss.length).comp len
  exact ((Procedure.tabulate (ea := listCode ContactPlacedGadgetProgram.inputCode)
    (eb := pointCode) (f := fun xs i =>
      ((ss.map (ContactPlacedGadgetProgram.position
        ((xs.drop (i / ss.length)).headD defaultEdge))).drop (i % ss.length)).headD (0, 0))
      (0, 0) (stepProgram ss)).comp
        (count.pair (Procedure.identity (listCode ContactPlacedGadgetProgram.inputCode)))).congrFun
          (by intro xs; rfl)

def firstSites : List ContactGadgetSite :=
  List.ofFn (fun s : Fin 2 => localToContact (localFirst s))

def secondSites : List ContactGadgetSite :=
  List.ofFn (fun i : Fin 4 =>
    let st : Fin 2 × Fin 2 := finProdFinEquiv.symm i
    localToContact (localSecond st.1 st.2))

def thirdFirstSites : List ContactGadgetSite :=
  List.ofFn (fun i : Fin 4 =>
    let st : Fin 2 × Fin 2 := finProdFinEquiv.symm i
    localToContact (localThird (Sum.inl st.1) st.2))

def thirdSecondSites : List ContactGadgetSite :=
  List.ofFn (fun sut : Fin 8 =>
    let st : Fin 4 × Fin 2 := finProdFinEquiv.symm sut
    let su : Fin 2 × Fin 2 := finProdFinEquiv.symm st.1
    localToContact (localThird (Sum.inr su) st.2))

def oldPoint (p : ℤ × ℤ) : ℚ × ℚ := (17 * (p.1 : ℚ), 17 * (p.2 : ℚ))

noncomputable opaque oldPointProgram : Procedure ContactCanonicalEdgeProgram.latticeCode
    pointCode oldPoint := by
  let x := Procedure.intToRat.comp (Procedure.first intCode intCode)
  let y := Procedure.intToRat.comp (Procedure.second intCode intCode)
  exact (Procedure.ratMul.comp
    ((Procedure.constant ContactCanonicalEdgeProgram.latticeCode ratCode 17).pair x)).pair
      (Procedure.ratMul.comp
        ((Procedure.constant ContactCanonicalEdgeProgram.latticeCode ratCode 17).pair y))

abbrev Input := List (ℤ × ℤ) × List EdgeInput

def inputCode : Input → List Bool :=
  prodCode (listCode ContactCanonicalEdgeProgram.latticeCode)
    (listCode ContactPlacedGadgetProgram.inputCode)

def positions (x : Input) : List (ℚ × ℚ) :=
  x.1.map oldPoint ++ block firstSites x.2 ++ block secondSites x.2 ++
    block thirdFirstSites x.2 ++ block thirdSecondSites x.2

noncomputable opaque oldProgram : Procedure inputCode (listCode pointCode)
    (fun x => x.1.map oldPoint) :=
  (Procedure.listMap (0, 0) (0, 0) oldPointProgram).comp (Procedure.first _ _)

noncomputable opaque listProgram (ss : List ContactGadgetSite) :
    Procedure inputCode (listCode pointCode) (fun x => block ss x.2) :=
  (blockProgram ss).comp (Procedure.second _ _)

noncomputable opaque program : Procedure inputCode (listCode pointCode) positions := by
  let append := Procedure.listAppend pointCode (0, 0)
  let a := append.comp (oldProgram.pair (listProgram firstSites))
  let b := append.comp (a.pair (listProgram secondSites))
  let c := append.comp (b.pair (listProgram thirdFirstSites))
  exact (append.comp (c.pair (listProgram thirdSecondSites))).congrFun
    (by intro x; simp only [positions, Function.comp_apply, List.append_assoc])

theorem positions_length (x : Input) :
    (positions x).length = x.1.length + 18 * x.2.length := by
  simp only [positions, List.length_append, List.length_map, block,
    List.length_range, firstSites, secondSites, thirdFirstSites, thirdSecondSites,
    List.length_ofFn]
  omega

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode
    (listCode pointCode) positions := program.toTM2

end ContinuumCoulomb.ContactGeometryBlockProgram

end

end OAI
