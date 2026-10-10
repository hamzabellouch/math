import OAI.Combinatorics.Crossing.PlanarDeterminant
import Mathlib.Tactic.FunProp
import Mathlib.Topology.Homeomorph.Defs

namespace OAI

noncomputable section
namespace Zarankiewicz

def crossingCoordinates (o u v x : Plane) : Plane :=
  (det2 (x-o) v/det2 u v,det2 u (x-o)/det2 u v)

def crossingCoordinateInverse (o u v s : Plane) : Plane := o+s.1 • u+s.2 • v

theorem crossingCoordinates_left_inverse (o u v : Plane) (h : det2 u v ≠ 0) (x : Plane) :
    crossingCoordinateInverse o u v (crossingCoordinates o u v x)=x := by
  have hc := mul_inv_cancel₀ h
  apply Prod.ext
  · dsimp [crossingCoordinateInverse,crossingCoordinates,det2] at *
    simp only [div_eq_mul_inv]
    linear_combination (x.1-o.1)*hc
  · dsimp [crossingCoordinateInverse,crossingCoordinates,det2] at *
    simp only [div_eq_mul_inv]
    linear_combination (x.2-o.2)*hc

theorem crossingCoordinates_right_inverse (o u v : Plane) (h : det2 u v ≠ 0) (s : Plane) :
    crossingCoordinates o u v (crossingCoordinateInverse o u v s)=s := by
  have hc := mul_inv_cancel₀ h
  apply Prod.ext
  · dsimp [crossingCoordinateInverse,crossingCoordinates,det2] at *
    simp only [div_eq_mul_inv]
    linear_combination s.1*hc
  · dsimp [crossingCoordinateInverse,crossingCoordinates,det2] at *
    simp only [div_eq_mul_inv]
    linear_combination s.2*hc

theorem crossingCoordinates_continuous (o u v : Plane) : Continuous (crossingCoordinates o u v) := by
  unfold crossingCoordinates det2
  fun_prop

theorem crossingCoordinateInverse_continuous (o u v : Plane) : Continuous (crossingCoordinateInverse o u v) := by
  unfold crossingCoordinateInverse
  fun_prop

def crossingCoordinateHomeomorph (o u v : Plane) (h : det2 u v ≠ 0) : Plane ≃ₜ Plane where
  toFun := crossingCoordinates o u v
  invFun := crossingCoordinateInverse o u v
  left_inv := crossingCoordinates_left_inverse o u v h
  right_inv := crossingCoordinates_right_inverse o u v h
  continuous_toFun := crossingCoordinates_continuous o u v
  continuous_invFun := crossingCoordinateInverse_continuous o u v

def crossingCoordinateChart (o u v : Plane) (h : det2 u v ≠ 0)
    (U : Set Plane) (hU : IsOpen U) : OpenPartialHomeomorph Plane Plane where
  toFun := crossingCoordinates o u v
  invFun := crossingCoordinateInverse o u v
  source := crossingCoordinates o u v ⁻¹' U
  target := U
  map_source' := fun {_} hx => hx
  map_target' := fun {s} hs => by
    change crossingCoordinates o u v (crossingCoordinateInverse o u v s) ∈ U
    rw [crossingCoordinates_right_inverse o u v h]
    exact hs
  left_inv' := fun {x} _ => crossingCoordinates_left_inverse o u v h x
  right_inv' := fun {s} _ => crossingCoordinates_right_inverse o u v h s
  continuousOn_toFun := (crossingCoordinates_continuous o u v).continuousOn
  continuousOn_invFun := (crossingCoordinateInverse_continuous o u v).continuousOn
  open_source := hU.preimage (crossingCoordinates_continuous o u v)
  open_target := hU

@[simp] theorem crossingCoordinates_origin (o u v : Plane) : crossingCoordinates o u v o=(0,0) := by
  simp [crossingCoordinates]

end Zarankiewicz

end

end OAI
