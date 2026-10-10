import OAI.Geometry.EinsteinFour.HighestCoordinates

namespace OAI

/-! The exact linear equations and their elementary eliminations. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- These are precisely the independent scalar trace and Bianchi equations. -/
structure Equations (c : Fin 50 → ℝ) : Prop where
  eq0 : c 0 + c 20 + c 35 + c 45 = 0
  eq1 : c 1 + c 21 + c 36 + c 46 = 0
  eq2 : c 2 + c 22 + c 37 + c 47 = 0
  eq3 : c 3 + c 23 + c 38 + c 48 = 0
  eq4 : c 4 + c 24 + c 39 + c 49 = 0
  eq5 : -c 5 - c 12 - c 18 = 0
  eq6 : c 0 - c 13 + c 17 = 0
  eq7 : c 2 + c 8 - c 15 = 0
  eq8 : c 3 - c 7 + c 10 = 0
  eq9 : -c 7 - c 11 - c 19 = 0
  eq10 : c 2 - c 14 + c 16 = 0
  eq11 : c 1 + c 9 - c 17 = 0
  eq12 : c 4 - c 6 + c 12 = 0
  eq17 : -c 20 - c 27 - c 33 = 0
  eq18 : c 5 - c 28 + c 32 = 0
  eq19 : c 7 + c 23 - c 30 = 0
  eq20 : c 8 - c 22 + c 25 = 0
  eq21 : -c 22 - c 26 - c 34 = 0
  eq22 : c 7 - c 29 + c 31 = 0
  eq23 : c 6 + c 24 - c 32 = 0
  eq24 : c 9 - c 21 + c 27 = 0
  eq29 : -c 25 - c 37 - c 43 = 0
  eq30 : c 10 - c 38 + c 42 = 0
  eq31 : c 12 + c 28 - c 40 = 0
  eq32 : c 13 - c 27 + c 35 = 0
  eq33 : -c 27 - c 36 - c 44 = 0
  eq34 : c 12 - c 39 + c 41 = 0
  eq35 : c 11 + c 29 - c 42 = 0
  eq36 : c 14 - c 26 + c 37 = 0

theorem Equations.pivot_0 {c : Fin 50 → ℝ} (h : Equations c) :
    c 0 = -(freeCoordinates c) 6 - (freeCoordinates c) 7 - 2 * (freeCoordinates c) 15 + (freeCoordinates c) 17 := by
  dsimp [freeCoordinates]
  linear_combination (-1) * h.eq1 + (1) * h.eq6 + (1) * h.eq11 + (-1) * h.eq24 + (1) * h.eq32 + (-2) * h.eq33

theorem Equations.pivot_1 {c : Fin 50 → ℝ} (h : Equations c) :
    c 1 = -(freeCoordinates c) 0 - (freeCoordinates c) 7 - (freeCoordinates c) 17 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq1

theorem Equations.pivot_2 {c : Fin 50 → ℝ} (h : Equations c) :
    c 2 = (freeCoordinates c) 2 + (freeCoordinates c) 5 - (freeCoordinates c) 8 - (freeCoordinates c) 18 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq2 + (1) * h.eq21

theorem Equations.pivot_3 {c : Fin 50 → ℝ} (h : Equations c) :
    c 3 = (freeCoordinates c) 3 - (freeCoordinates c) 4 - (freeCoordinates c) 9 + (freeCoordinates c) 13 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq8 + (1) * h.eq22 + (-1) * h.eq30

theorem Equations.pivot_4 {c : Fin 50 → ℝ} (h : Equations c) :
    c 4 = -(freeCoordinates c) 1 - (freeCoordinates c) 10 - (freeCoordinates c) 20 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq4

theorem Equations.pivot_5 {c : Fin 50 → ℝ} (h : Equations c) :
    c 5 = -(freeCoordinates c) 10 + (freeCoordinates c) 11 + 2 * (freeCoordinates c) 12 + (freeCoordinates c) 20 := by
  dsimp [freeCoordinates]
  linear_combination (-1) * h.eq4 + (1) * h.eq12 + (1) * h.eq18 + (1) * h.eq23 + (1) * h.eq31 + (-2) * h.eq34

theorem Equations.pivot_6 {c : Fin 50 → ℝ} (h : Equations c) :
    c 6 = -(freeCoordinates c) 1 - (freeCoordinates c) 12 - (freeCoordinates c) 20 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq4 + (-1) * h.eq12 + (1) * h.eq34

theorem Equations.pivot_7 {c : Fin 50 → ℝ} (h : Equations c) :
    c 7 = (freeCoordinates c) 3 - (freeCoordinates c) 4 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq22

theorem Equations.pivot_8 {c : Fin 50 → ℝ} (h : Equations c) :
    c 8 = -(freeCoordinates c) 2 - (freeCoordinates c) 5 + (freeCoordinates c) 8 + (freeCoordinates c) 14 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq20 + (-1) * h.eq21 + (1) * h.eq29

theorem Equations.pivot_9 {c : Fin 50 → ℝ} (h : Equations c) :
    c 9 = (freeCoordinates c) 0 + (freeCoordinates c) 7 + (freeCoordinates c) 15 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq24 + (1) * h.eq33

theorem Equations.pivot_10 {c : Fin 50 → ℝ} (h : Equations c) :
    c 10 = (freeCoordinates c) 9 - (freeCoordinates c) 13 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq30

theorem Equations.pivot_11 {c : Fin 50 → ℝ} (h : Equations c) :
    c 11 = -(freeCoordinates c) 3 + (freeCoordinates c) 13 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq35

theorem Equations.pivot_12 {c : Fin 50 → ℝ} (h : Equations c) :
    c 12 = (freeCoordinates c) 10 - (freeCoordinates c) 12 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq34

theorem Equations.pivot_13 {c : Fin 50 → ℝ} (h : Equations c) :
    c 13 = -(freeCoordinates c) 6 - (freeCoordinates c) 7 - (freeCoordinates c) 15 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq32 + (-1) * h.eq33

theorem Equations.pivot_14 {c : Fin 50 → ℝ} (h : Equations c) :
    c 14 = (freeCoordinates c) 2 - (freeCoordinates c) 8 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq36

theorem Equations.pivot_15 {c : Fin 50 → ℝ} (h : Equations c) :
    c 15 = (freeCoordinates c) 14 - (freeCoordinates c) 18 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq2 + (-1) * h.eq7 + (1) * h.eq20 + (1) * h.eq29

theorem Equations.pivot_16 {c : Fin 50 → ℝ} (h : Equations c) :
    c 16 = -(freeCoordinates c) 5 + (freeCoordinates c) 18 := by
  dsimp [freeCoordinates]
  linear_combination (-1) * h.eq2 + (1) * h.eq10 + (-1) * h.eq21 + (1) * h.eq36

theorem Equations.pivot_17 {c : Fin 50 → ℝ} (h : Equations c) :
    c 17 = (freeCoordinates c) 15 - (freeCoordinates c) 17 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq1 + (-1) * h.eq11 + (1) * h.eq24 + (1) * h.eq33

theorem Equations.pivot_18 {c : Fin 50 → ℝ} (h : Equations c) :
    c 18 = -(freeCoordinates c) 11 - (freeCoordinates c) 12 - (freeCoordinates c) 20 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq4 + (-1) * h.eq5 + (-1) * h.eq12 + (-1) * h.eq18 + (-1) * h.eq23 + (-1) * h.eq31 + (1) * h.eq34

theorem Equations.pivot_19 {c : Fin 50 → ℝ} (h : Equations c) :
    c 19 = (freeCoordinates c) 4 - (freeCoordinates c) 13 := by
  dsimp [freeCoordinates]
  linear_combination (-1) * h.eq9 + (-1) * h.eq22 + (-1) * h.eq35

theorem Equations.pivot_20 {c : Fin 50 → ℝ} (h : Equations c) :
    c 20 = (freeCoordinates c) 7 + 2 * (freeCoordinates c) 15 - (freeCoordinates c) 16 - (freeCoordinates c) 17 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq0 + (1) * h.eq1 + (-1) * h.eq6 + (-1) * h.eq11 + (1) * h.eq24 + (-1) * h.eq32 + (2) * h.eq33

theorem Equations.pivot_22 {c : Fin 50 → ℝ} (h : Equations c) :
    c 22 = -(freeCoordinates c) 2 - (freeCoordinates c) 5 := by
  dsimp [freeCoordinates]
  linear_combination (-1) * h.eq21

theorem Equations.pivot_23 {c : Fin 50 → ℝ} (h : Equations c) :
    c 23 = -(freeCoordinates c) 3 + (freeCoordinates c) 4 - (freeCoordinates c) 13 - (freeCoordinates c) 19 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq3 + (-1) * h.eq8 + (-1) * h.eq22 + (1) * h.eq30

theorem Equations.pivot_25 {c : Fin 50 → ℝ} (h : Equations c) :
    c 25 = -(freeCoordinates c) 8 - (freeCoordinates c) 14 := by
  dsimp [freeCoordinates]
  linear_combination (-1) * h.eq29

theorem Equations.pivot_27 {c : Fin 50 → ℝ} (h : Equations c) :
    c 27 = -(freeCoordinates c) 7 - (freeCoordinates c) 15 := by
  dsimp [freeCoordinates]
  linear_combination (-1) * h.eq33

theorem Equations.pivot_28 {c : Fin 50 → ℝ} (h : Equations c) :
    c 28 = -(freeCoordinates c) 10 + (freeCoordinates c) 11 + (freeCoordinates c) 12 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq31 + (-1) * h.eq34

theorem Equations.pivot_30 {c : Fin 50 → ℝ} (h : Equations c) :
    c 30 = -(freeCoordinates c) 13 - (freeCoordinates c) 19 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq3 + (-1) * h.eq8 + (-1) * h.eq19 + (1) * h.eq30

theorem Equations.pivot_32 {c : Fin 50 → ℝ} (h : Equations c) :
    c 32 = -(freeCoordinates c) 12 - (freeCoordinates c) 20 := by
  dsimp [freeCoordinates]
  linear_combination (1) * h.eq4 + (-1) * h.eq12 + (-1) * h.eq23 + (1) * h.eq34

theorem Equations.pivot_33 {c : Fin 50 → ℝ} (h : Equations c) :
    c 33 = -(freeCoordinates c) 15 + (freeCoordinates c) 16 + (freeCoordinates c) 17 := by
  dsimp [freeCoordinates]
  linear_combination (-1) * h.eq0 + (-1) * h.eq1 + (1) * h.eq6 + (1) * h.eq11 + (-1) * h.eq17 + (-1) * h.eq24 + (1) * h.eq32 + (-1) * h.eq33


end
end PositiveEinsteinFour.HighestHessian

end OAI
