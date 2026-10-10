import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.GaussPositionCell
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.TransportedNodes

namespace OAI

/-! Identify tensor quadrature with the actual eight equal point masses and
with the already separated Gauss lattice used by the nuclear construction. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

def gaussNodeTriple : (Fin 3 → Fin 2) ≃ Fin 2 × Fin 2 × Fin 2 where
  toFun v := (v 0,v 1,v 2)
  invFun p := ![p.1,p.2.1,p.2.2]
  left_inv v := by ext i; fin_cases i <;> rfl
  right_inv p := rfl

theorem gaussTensor3_eq_node_sum (f : ℝ → ℝ → ℝ → ℝ) :
    gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (f x y))) =
      ∑ v : Fin 3 → Fin 2, f (gaussNode (v 0)) (gaussNode (v 1)) (gaussNode (v 2)) := by
  have h := Fintype.sum_equiv gaussNodeTriple
    (fun v => f (gaussNode (v 0)) (gaussNode (v 1)) (gaussNode (v 2)))
    (fun p => f (gaussNode p.1) (gaussNode p.2.1) (gaussNode p.2.2)) (fun _ => rfl)
  rw [h]
  simp only [Fintype.sum_prod_type,Fin.sum_univ_two,gaussNode,Fin.isValue,ite_true]
  rfl

theorem positionCellGauss_eq_node_sum (b : Position) (h : ℝ) (f : Position → ℝ) :
    positionCellGauss b h f = (h^3/8)*∑ v : Fin 3 → Fin 2,
      f (cubePoint b (h/2) (gaussNode (v 0)) (gaussNode (v 1)) (gaussNode (v 2))) := by
  rw [positionCellGauss,gaussTensor3_eq_node_sum]
  congr 1
  ring

def gaussCellCenter (h : ℝ) (k : Fin 3 → ℤ) : Position :=
  WithLp.toLp 2 (fun i => h*(k i:ℝ))

theorem cubePoint_gaussLatticePoint (h : ℝ) (k : Fin 3 → ℤ) (v : Fin 3 → Fin 2) :
    cubePoint (gaussCellCenter h k) (h/2) (gaussNode (v 0)) (gaussNode (v 1)) (gaussNode (v 2)) =
      gaussLatticePoint h (k,v) := by
  ext i
  fin_cases i <;> simp [cubePoint,gaussCellCenter,gaussLatticePoint] <;> ring

theorem gaussCell_quadrature_lattice (h : ℝ) (k : Fin 3 → ℤ) (f : Position → ℝ) :
    positionCellGauss (gaussCellCenter h k) h f =
      (h^3/8)*∑ v : Fin 3 → Fin 2, f (gaussLatticePoint h (k,v)) := by
  rw [positionCellGauss_eq_node_sum]
  simp only [cubePoint_gaussLatticePoint]

end ContinuumCoulomb

end

end OAI
