import OAI.NumberTheory.Ostmann.Tree.QuartetHeld
import OAI.NumberTheory.Ostmann.Tree.QuartetPairValues

namespace OAI

namespace Ostmann.Tree.Quartet
noncomputable section
variable {F : Type*} [Field F]

namespace NodeInput
variable {d : ℕ}

theorem evaluate_eq_zero (N : NodeInput F d) (hp : N.pivot = 0)
    (g : F → ℂ) (incoming : F) :
    N.parameters.evaluate g N.D N.Xleft N.Xright incoming N.leaves = 0 := by
  classical
  simp only [parameters, Parameters.evaluate]
  split_ifs with h
  · rfl
  · exact False.elim (h hp)

def ofParameters (P : Parameters F (d+1)) (D Xleft Xright : Fˣ)
    (M : Leaves (d+1) → Fˣ) : NodeInput F d :=
  match P with | .branch s a b u L R => ⟨s,a,b,u,D,Xleft,Xright,L,R,M⟩

def ofDiagram (T : Diagram F (d+1)) (M : Leaves (d+1) → Fˣ) : NodeInput F d :=
  ofParameters T.parameters T.denominator T.rootLeft T.rootRight M

theorem ofDiagram_parameters (T : Diagram F (d+1)) (M : Leaves (d+1) → Fˣ) :
    (ofDiagram T M).parameters = T.parameters := by
  cases he : T.parameters; simp only [ofDiagram, ofParameters, he, parameters]

theorem diagram_value (T : Diagram F (d+1)) (M : Leaves (d+1) → Fˣ) (g : F → ℂ) :
    T.value g M =
      (ofDiagram T M).parameters.evaluate g (ofDiagram T M).D
        (ofDiagram T M).Xleft (ofDiagram T M).Xright 0 (ofDiagram T M).leaves := by
  cases he : T.parameters
  simp only [ofDiagram, ofParameters, Diagram.value, Parameters.value, he, parameters]

theorem descend_evaluate (N : NodeInput F (d+1)) (hp : N.pivot ≠ 0)
    (g : F → ℂ) (incoming : F) :
    N.parameters.evaluate g N.D N.Xleft N.Xright incoming N.leaves =
      (N.leftNode hp).parameters.evaluate g (N.leftNode hp).D
        (N.leftNode hp).Xleft (N.leftNode hp).Xright (N.leftArgument hp:F)
        (N.leftNode hp).leaves *
      (N.rightNode hp).parameters.evaluate g (N.rightNode hp).D
        (N.rightNode hp).Xleft (N.rightNode hp).Xright (N.rightArgument hp:F)
        (N.rightNode hp).leaves := by
  rw [evaluate_eq N hp g incoming]
  cases hl : N.left with
  | branch sl al bl ul LL LR =>
    cases hr : N.right with
    | branch sr ar br ur RL RR =>
      simp only [leftNode, rightNode, hl, hr, parameters]

def orientation (freeRight : Bool) : Fˣ := if freeRight then -1 else 1

def orientedSign (N : NodeInput F 0) (freeRight : Bool) : Bool :=
  if freeRight then leafSign N.right else leafSign N.left

def orientedRatio (N : NodeInput F 0) (hp : N.pivot ≠ 0) (freeRight : Bool) : Fˣ :=
  if freeRight then N.rightArgument hp/N.leftArgument hp
  else N.leftArgument hp/N.rightArgument hp

theorem bottom_evaluate_oriented (N : NodeInput F 0) (hp : N.pivot ≠ 0)
    (hopp : N.parameters.bottomOpposite) (g : F → ℂ) (incoming : F)
    (freeRight : Bool) :
    N.parameters.evaluate g N.D N.Xleft N.Xright incoming N.leaves =
      pairValue g (N.orientedSign freeRight) (orientation freeRight) (N.argument:F)
        (N.orientedRatio hp freeRight:F) := by
  cases freeRight
  · exact bottom_evaluate_left N hp hopp g incoming
  · exact bottom_evaluate_right N hp hopp g incoming

theorem quartet_evaluate_oriented (N : NodeInput F 1) (hp : N.pivot ≠ 0)
    (hcons : N.parameters.consistent) (hopp : N.parameters.bottomOpposite)
    (hl : (N.leftNode hp).pivot ≠ 0) (hr : (N.rightNode hp).pivot ≠ 0)
    (g : F → ℂ) (incoming : F) (leftFreeRight rightFreeRight : Bool) :
    N.parameters.evaluate g N.D N.Xleft N.Xright incoming N.leaves =
      pairValue g ((N.leftNode hp).orientedSign leftFreeRight) (orientation leftFreeRight)
        (N.leftArgument hp:F) ((N.leftNode hp).orientedRatio hl leftFreeRight:F) *
      pairValue g ((N.rightNode hp).orientedSign rightFreeRight) (orientation rightFreeRight)
        (N.rightArgument hp:F) ((N.rightNode hp).orientedRatio hr rightFreeRight:F) := by
  have hop : N.left.bottomOpposite ∧ N.right.bottomOpposite := hopp
  have hopL : (N.leftNode hp).parameters.bottomOpposite := by
    cases he : N.left with
    | branch s a b u L R => simpa only [leftNode, he, parameters] using hop.1
  have hopR : (N.rightNode hp).parameters.bottomOpposite := by
    cases he : N.right with
    | branch s a b u L R => simpa only [rightNode, he, parameters] using hop.2
  have hc : N.left.childConsistent (N.u*N.a) ∧ N.right.childConsistent (N.u*N.b) ∧
      N.left.consistent ∧ N.right.consistent := hcons
  rw [descend_evaluate N hp g incoming,
    bottom_evaluate_oriented _ hl hopL g _ leftFreeRight,
    bottom_evaluate_oriented _ hr hopR g _ rightFreeRight,
    leftNode_argument N hp hc.1, rightNode_argument N hp hc.2.1]

end NodeInput
end
end Ostmann.Tree.Quartet

end OAI
