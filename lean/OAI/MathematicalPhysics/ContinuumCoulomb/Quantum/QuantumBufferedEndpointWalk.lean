import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedArms
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedLanes

namespace OAI

/-! Actual unit-step walks join the degree-three vertices through their separated lanes. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

def routeVertex (v : Fin M.n) : ℕ × ℕ :=
  qmaFineGridNat (M.qubitSlots.site v)

def placedVertex (v : Fin M.n) : ℕ × ℕ :=
  qmaBufferedCellPoint (9*B+3) (M.routeVertex v) (17,17)

def endpointColors (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (v : Fin M.n)
    (a : Fin 3) : ℕ := ((M.endpointPorts hd v).slot a).val

theorem endpointColors_assigned (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) :
    M.endpointColors hd v ((M.endpointPorts hd v).assign e) = (M.laneColor e.val).val :=
  congrArg Fin.val ((M.endpointPorts hd v).aligned e)

def endpointArmLength (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) : ℕ :=
  qmaBufferedArmLength (M.endpointColors hd v) (fun _ => false) ((M.endpointPorts hd v).assign e)

def endpointArmPoint (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) (k : ℕ) : ℕ × ℕ :=
  qmaBufferedCellPoint (9*B+3) (M.routeVertex v)
    (qmaBufferedArmPoint (M.endpointColors hd v) (fun _ => false) ((M.endpointPorts hd v).assign e) k)

@[simp] theorem endpointArm_zero (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) : M.endpointArmPoint hd v e 0 = M.placedVertex v := by
  simp [endpointArmPoint,placedVertex]

@[simp] theorem endpointArm_last (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) :
    M.endpointArmPoint hd v e (M.endpointArmLength hd v e) =
      qmaLanePoint (M.spacedColor e.val) (M.routeVertex v) := by
  dsimp only [endpointArmPoint,endpointArmLength]
  rw [qmaBufferedArm_last]
  change qmaBufferedCellPoint (9*B+3) (M.routeVertex v)
    (8*(M.endpointColors hd v ((M.endpointPorts hd v).assign e)+3),
     8*(M.endpointColors hd v ((M.endpointPorts hd v).assign e)+3)) = _
  rw [M.endpointColors_assigned]
  exact (qmaSpacedEndpoint (M.routeVertex v) ((M.laneColor e.val).castAdd 3)).symm

theorem endpointArm_step (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) (k : ℕ) (hk : k < M.endpointArmLength hd v e) :
    qmaSquareGrid.Adj (M.endpointArmPoint hd v e k) (M.endpointArmPoint hd v e (k+1)) := by
  have h := qmaBufferedArm_step (M.endpointColors hd v) (fun _ => false)
    ((M.endpointPorts hd v).assign e) k hk
  simpa only [endpointArmPoint,qmaBufferedCellPoint,qmaSquareGrid,Nat.dist_add_add_left] using h

theorem endpointArm_length_bound (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) : M.endpointArmLength hd v e ≤ 16*(9*B+6)+2 :=
  qmaBufferedArm_length_bound (M.endpointColors hd v) (fun _ => false)
    (fun a => ((M.endpointPorts hd v).slot a).isLt) _

def endpointArmWalk (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) :
    qmaSquareGrid.Walk (M.placedVertex v) (qmaLanePoint (M.spacedColor e.val) (M.routeVertex v)) :=
  (qmaGridWalk (M.endpointArmPoint hd v e) (M.endpointArmLength hd v e)
    (M.endpointArm_step hd v e)).copy (M.endpointArm_zero hd v e) (M.endpointArm_last hd v e)

@[simp] theorem endpointArmWalk_length (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) :
    (M.endpointArmWalk hd v e).length = M.endpointArmLength hd v e := by
  simp [endpointArmWalk,SimpleGraph.Walk.length_copy,qmaGridWalk_length]

def spacedWalk (e : M.Term) :
    qmaSquareGrid.Walk (qmaLanePoint (M.spacedColor e) (M.routeVertex (M.left e)))
      (qmaLanePoint (M.spacedColor e) (M.routeVertex (M.right e))) :=
  let p := qmaLanePoint (M.spacedColor e) (M.routeVertex (M.left e))
  let q := qmaLanePoint (M.spacedColor e) (M.routeVertex (M.right e))
  (qmaGridWalk (qmaManhattanPoint p q) (qmaManhattanLength p q)
    (qmaManhattanPoint_adj p q)).copy (qmaManhattanPoint_zero p q) (qmaManhattanPoint_last p q)

theorem spacedWalk_length (e : M.Term) : (M.spacedWalk e).length ≤ 8*(9*B+9)*(3*A+2) := by
  dsimp only [spacedWalk]
  rw [SimpleGraph.Walk.length_copy,qmaGridWalk_length]
  exact M.spaced_length e

def bufferedWalk (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    qmaSquareGrid.Walk (M.placedVertex (M.left e)) (M.placedVertex (M.right e)) :=
  ((M.endpointArmWalk hd (M.left e) ⟨e,Or.inl rfl⟩).append (M.spacedWalk e)).append
    (M.endpointArmWalk hd (M.right e) ⟨e,Or.inr rfl⟩).reverse

theorem bufferedWalk_length (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    (M.bufferedWalk hd e).length ≤ 2*(16*(9*B+6)+2)+8*(9*B+9)*(3*A+2) := by
  have hl := M.endpointArm_length_bound hd (M.left e) ⟨e,Or.inl rfl⟩
  have hr := M.endpointArm_length_bound hd (M.right e) ⟨e,Or.inr rfl⟩
  have hg := M.spacedWalk_length e
  simp only [bufferedWalk,SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_reverse,
    endpointArmWalk_length]
  omega

def bufferedPath (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    qmaSquareGrid.Path (M.placedVertex (M.left e)) (M.placedVertex (M.right e)) :=
  (M.bufferedWalk hd e).toPath

theorem bufferedPath_length (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    (M.bufferedPath hd e).val.length ≤ 2*(16*(9*B+6)+2)+8*(9*B+9)*(3*A+2) :=
  ((M.bufferedWalk hd e).length_bypass_le_length).trans (M.bufferedWalk_length hd e)

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
