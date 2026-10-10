import OAI.Combinatorics.PolynomialVacuum.Pairing.RowConfigurations
import OAI.Combinatorics.PolynomialVacuum.Cylinder.LayerCurrent

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical PolynomialVacuumCylinder

@[simp] theorem streamEndpoint_pos (N : ℕ) (a : Spin) (r : Fin (N+1) → Spin) :
    streamEndpoint a r=r (Fin.last N) := rfl

private theorem fin_zero_prev (N : ℕ) : (0-1 : Fin (N+1))=Fin.last N := by
  apply Fin.ext
  simp

private theorem fin_succ_prev (N : ℕ) (j : Fin N) :
    (j.succ-1 : Fin (N+1))=j.castSucc := by
  apply Fin.ext
  rw [Fin.val_sub_one_of_ne_zero (by simp)]
  simp

theorem incomingStream_periodic (N : ℕ) (r : Fin (N+1) → Spin) (j : Fin (N+1)) :
    incomingStream (r (Fin.last N)) r j=r (j-1) := by
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [fin_zero_prev]
    rfl
  · rw [fin_succ_prev]
    rfl

theorem physicalTransfer_periodic (N : ℕ) (κ : ℂ) (out inp : Fin (N+1) → Spin) :
    physicalTransfer (N+1) κ out inp=∑ r : Fin (N+1) → Spin,∑ k : Fin (N+1) → Spin,
      κ^charge (r (Fin.last N)) * ∏j : Fin (N+1),
        honeycombPiece (out j,r j) (r (j-1),inp j) (k j) := by
  rw [physicalTransfer_configurations,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [rowConfigurationWeight,streamEndpoint_pos]
  rw [Finset.sum_eq_single (r (Fin.last N))]
  · simp only [ite_true,incomingStream_periodic]
  · intro a _ ha
    simp [Ne.symm ha]
  · simp

 
noncomputable def rowCoordinate (N : ℕ) : Fin (N+1) ≃ ZMod (N+1) :=
  (ZMod.finEquiv (N+1)).toEquiv.trans (Equiv.neg _)

theorem rowCoordinate_prev (N : ℕ) (j : Fin (N+1)) :
    rowCoordinate N (j-1)=rowCoordinate N j+1 := by
  change -(ZMod.finEquiv (N+1) (j-1))= -(ZMod.finEquiv (N+1) j)+1
  rw [map_sub,map_one]
  ring

theorem rowCoordinate_last (N : ℕ) : rowCoordinate N (Fin.last N)=1 := by
  rw [← fin_zero_prev]
  rw [rowCoordinate_prev]
  change -(ZMod.finEquiv (N+1) 0)+1=1
  simp

noncomputable def cylinderState (N : ℕ) (s : Fin (N+1) → Spin) : ZMod (N+1) → Spin :=
  fun i => s ((rowCoordinate N).symm i)

@[simp] theorem cylinderState_coordinate (N : ℕ) (s : Fin (N+1) → Spin) (j : Fin (N+1)) :
    cylinderState N s (rowCoordinate N j)=s j := by simp [cylinderState]

theorem cylinderState_next (N : ℕ) (s : Fin (N+1) → Spin) (j : Fin (N+1)) :
    cylinderState N s (rowCoordinate N j+1)=s (j-1) := by
  rw [← rowCoordinate_prev,cylinderState_coordinate]

 

theorem physicalTransfer_currents (N : ℕ) (κ : ℂ) (out inp : Fin (N+1) → Spin) :
    physicalTransfer (N+1) κ out inp=∑ r : Fin (N+1) → Spin,∑ k : Fin (N+1) → Spin,
      κ^charge (cylinderState N r 1) * ∏i : ZMod (N+1),
        localCurrentWeight (layerCurrent (cylinderState N out) (cylinderState N inp)
          (cylinderState N r) (cylinderState N k)) (.up i 0)*
        localCurrentWeight (layerCurrent (cylinderState N out) (cylinderState N inp)
          (cylinderState N r) (cylinderState N k)) (.down i 0) := by
  rw [physicalTransfer_periodic]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro k _
  rw [← layer_weight_telescopes]
  have hr : cylinderState N r 1=r (Fin.last N) := by
    rw [← rowCoordinate_last N,cylinderState_coordinate]
  rw [hr]
  congr 1
  rw [← (rowCoordinate N).prod_comp]
  simp only [cylinderState_coordinate,cylinderState_next]

end PolynomialVacuumAlgebra

end OAI
