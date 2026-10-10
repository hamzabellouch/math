import OAI.Geometry.EinsteinFour.TraceHessian

namespace OAI

/-! The undetermined Hessian in concrete quaternion coordinates. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- A symmetric derivative array from its ten matrix entries. -/
def symmetricArray (m : Fin 10 → Mat) : Hessian :=
  ![![m 0, m 1, m 2, m 3], ![m 1, m 4, m 5, m 6],
    ![m 2, m 5, m 7, m 8], ![m 3, m 6, m 8, m 9]]

/-- All fifty coordinates before imposing derivative trace and Bianchi. -/
def rawEntries (c : Fin 50 → ℝ) : Fin 10 → Mat :=
  ![
    ofCoordinates (c 0) (c 1) (c 2) (c 3) (c 4),
    ofCoordinates (c 5) (c 6) (c 7) (c 8) (c 9),
    ofCoordinates (c 10) (c 11) (c 12) (c 13) (c 14),
    ofCoordinates (c 15) (c 16) (c 17) (c 18) (c 19),
    ofCoordinates (c 20) (c 21) (c 22) (c 23) (c 24),
    ofCoordinates (c 25) (c 26) (c 27) (c 28) (c 29),
    ofCoordinates (c 30) (c 31) (c 32) (c 33) (c 34),
    ofCoordinates (c 35) (c 36) (c 37) (c 38) (c 39),
    ofCoordinates (c 40) (c 41) (c 42) (c 43) (c 44),
    ofCoordinates (c 45) (c 46) (c 47) (c 48) (c 49)]

def raw (c : Fin 50 → ℝ) : Hessian := symmetricArray (rawEntries c)

@[simp] theorem rawEntries_0 (c : Fin 50 → ℝ) :
    rawEntries c 0 = ofCoordinates (c 0) (c 1) (c 2) (c 3) (c 4) := rfl

@[simp] theorem rawEntries_1 (c : Fin 50 → ℝ) :
    rawEntries c 1 = ofCoordinates (c 5) (c 6) (c 7) (c 8) (c 9) := rfl

@[simp] theorem rawEntries_2 (c : Fin 50 → ℝ) :
    rawEntries c 2 = ofCoordinates (c 10) (c 11) (c 12) (c 13) (c 14) := rfl

@[simp] theorem rawEntries_3 (c : Fin 50 → ℝ) :
    rawEntries c 3 = ofCoordinates (c 15) (c 16) (c 17) (c 18) (c 19) := rfl

@[simp] theorem rawEntries_4 (c : Fin 50 → ℝ) :
    rawEntries c 4 = ofCoordinates (c 20) (c 21) (c 22) (c 23) (c 24) := rfl

@[simp] theorem rawEntries_5 (c : Fin 50 → ℝ) :
    rawEntries c 5 = ofCoordinates (c 25) (c 26) (c 27) (c 28) (c 29) := rfl

@[simp] theorem rawEntries_6 (c : Fin 50 → ℝ) :
    rawEntries c 6 = ofCoordinates (c 30) (c 31) (c 32) (c 33) (c 34) := rfl

@[simp] theorem rawEntries_7 (c : Fin 50 → ℝ) :
    rawEntries c 7 = ofCoordinates (c 35) (c 36) (c 37) (c 38) (c 39) := rfl

@[simp] theorem rawEntries_8 (c : Fin 50 → ℝ) :
    rawEntries c 8 = ofCoordinates (c 40) (c 41) (c 42) (c 43) (c 44) := rfl

@[simp] theorem rawEntries_9 (c : Fin 50 → ℝ) :
    rawEntries c 9 = ofCoordinates (c 45) (c 46) (c 47) (c 48) (c 49) := rfl


@[simp] theorem raw_0_0 (c : Fin 50 → ℝ) :
    raw c 0 0 = ofCoordinates (c 0) (c 1) (c 2) (c 3) (c 4) := rfl

@[simp] theorem raw_0_1 (c : Fin 50 → ℝ) :
    raw c 0 1 = ofCoordinates (c 5) (c 6) (c 7) (c 8) (c 9) := rfl

@[simp] theorem raw_0_2 (c : Fin 50 → ℝ) :
    raw c 0 2 = ofCoordinates (c 10) (c 11) (c 12) (c 13) (c 14) := rfl

@[simp] theorem raw_0_3 (c : Fin 50 → ℝ) :
    raw c 0 3 = ofCoordinates (c 15) (c 16) (c 17) (c 18) (c 19) := rfl

@[simp] theorem raw_1_0 (c : Fin 50 → ℝ) :
    raw c 1 0 = ofCoordinates (c 5) (c 6) (c 7) (c 8) (c 9) := rfl

@[simp] theorem raw_1_1 (c : Fin 50 → ℝ) :
    raw c 1 1 = ofCoordinates (c 20) (c 21) (c 22) (c 23) (c 24) := rfl

@[simp] theorem raw_1_2 (c : Fin 50 → ℝ) :
    raw c 1 2 = ofCoordinates (c 25) (c 26) (c 27) (c 28) (c 29) := rfl

@[simp] theorem raw_1_3 (c : Fin 50 → ℝ) :
    raw c 1 3 = ofCoordinates (c 30) (c 31) (c 32) (c 33) (c 34) := rfl

@[simp] theorem raw_2_0 (c : Fin 50 → ℝ) :
    raw c 2 0 = ofCoordinates (c 10) (c 11) (c 12) (c 13) (c 14) := rfl

@[simp] theorem raw_2_1 (c : Fin 50 → ℝ) :
    raw c 2 1 = ofCoordinates (c 25) (c 26) (c 27) (c 28) (c 29) := rfl

@[simp] theorem raw_2_2 (c : Fin 50 → ℝ) :
    raw c 2 2 = ofCoordinates (c 35) (c 36) (c 37) (c 38) (c 39) := rfl

@[simp] theorem raw_2_3 (c : Fin 50 → ℝ) :
    raw c 2 3 = ofCoordinates (c 40) (c 41) (c 42) (c 43) (c 44) := rfl

@[simp] theorem raw_3_0 (c : Fin 50 → ℝ) :
    raw c 3 0 = ofCoordinates (c 15) (c 16) (c 17) (c 18) (c 19) := rfl

@[simp] theorem raw_3_1 (c : Fin 50 → ℝ) :
    raw c 3 1 = ofCoordinates (c 30) (c 31) (c 32) (c 33) (c 34) := rfl

@[simp] theorem raw_3_2 (c : Fin 50 → ℝ) :
    raw c 3 2 = ofCoordinates (c 40) (c 41) (c 42) (c 43) (c 44) := rfl

@[simp] theorem raw_3_3 (c : Fin 50 → ℝ) :
    raw c 3 3 = ofCoordinates (c 45) (c 46) (c 47) (c 48) (c 49) := rfl


/-- The twenty-one free coordinates after the actual tensor constraints. -/
def entries (c : Fin 21 → ℝ) : Fin 10 → Mat :=
  ![
    ofCoordinates (-c 6 - c 7 - 2 * c 15 + c 17) (-c 0 - c 7 - c 17) (c 2 + c 5 - c 8 - c 18) (c 3 - c 4 - c 9 + c 13) (-c 1 - c 10 - c 20),
    ofCoordinates (-c 10 + c 11 + 2 * c 12 + c 20) (-c 1 - c 12 - c 20) (c 3 - c 4) (-c 2 - c 5 + c 8 + c 14) (c 0 + c 7 + c 15),
    ofCoordinates (c 9 - c 13) (-c 3 + c 13) (c 10 - c 12) (-c 6 - c 7 - c 15) (c 2 - c 8),
    ofCoordinates (c 14 - c 18) (-c 5 + c 18) (c 15 - c 17) (-c 11 - c 12 - c 20) (c 4 - c 13),
    ofCoordinates (c 7 + 2 * c 15 - c 16 - c 17) (c 0) (-c 2 - c 5) (-c 3 + c 4 - c 13 - c 19) (c 1),
    ofCoordinates (-c 8 - c 14) (c 2) (-c 7 - c 15) (-c 10 + c 11 + c 12) (c 3),
    ofCoordinates (-c 13 - c 19) (c 4) (-c 12 - c 20) (-c 15 + c 16 + c 17) (c 5),
    ofCoordinates (c 6) (c 7) (c 8) (c 9) (c 10),
    ofCoordinates (c 11) (c 12) (c 13) (c 14) (c 15),
    ofCoordinates (c 16) (c 17) (c 18) (c 19) (c 20)]

def highest (c : Fin 21 → ℝ) : Hessian := symmetricArray (entries c)

@[simp] theorem entries_0 (c : Fin 21 → ℝ) :
    entries c 0 = ofCoordinates (-c 6 - c 7 - 2 * c 15 + c 17) (-c 0 - c 7 - c 17) (c 2 + c 5 - c 8 - c 18) (c 3 - c 4 - c 9 + c 13) (-c 1 - c 10 - c 20) := rfl

@[simp] theorem entries_1 (c : Fin 21 → ℝ) :
    entries c 1 = ofCoordinates (-c 10 + c 11 + 2 * c 12 + c 20) (-c 1 - c 12 - c 20) (c 3 - c 4) (-c 2 - c 5 + c 8 + c 14) (c 0 + c 7 + c 15) := rfl

@[simp] theorem entries_2 (c : Fin 21 → ℝ) :
    entries c 2 = ofCoordinates (c 9 - c 13) (-c 3 + c 13) (c 10 - c 12) (-c 6 - c 7 - c 15) (c 2 - c 8) := rfl

@[simp] theorem entries_3 (c : Fin 21 → ℝ) :
    entries c 3 = ofCoordinates (c 14 - c 18) (-c 5 + c 18) (c 15 - c 17) (-c 11 - c 12 - c 20) (c 4 - c 13) := rfl

@[simp] theorem entries_4 (c : Fin 21 → ℝ) :
    entries c 4 = ofCoordinates (c 7 + 2 * c 15 - c 16 - c 17) (c 0) (-c 2 - c 5) (-c 3 + c 4 - c 13 - c 19) (c 1) := rfl

@[simp] theorem entries_5 (c : Fin 21 → ℝ) :
    entries c 5 = ofCoordinates (-c 8 - c 14) (c 2) (-c 7 - c 15) (-c 10 + c 11 + c 12) (c 3) := rfl

@[simp] theorem entries_6 (c : Fin 21 → ℝ) :
    entries c 6 = ofCoordinates (-c 13 - c 19) (c 4) (-c 12 - c 20) (-c 15 + c 16 + c 17) (c 5) := rfl

@[simp] theorem entries_7 (c : Fin 21 → ℝ) :
    entries c 7 = ofCoordinates (c 6) (c 7) (c 8) (c 9) (c 10) := rfl

@[simp] theorem entries_8 (c : Fin 21 → ℝ) :
    entries c 8 = ofCoordinates (c 11) (c 12) (c 13) (c 14) (c 15) := rfl

@[simp] theorem entries_9 (c : Fin 21 → ℝ) :
    entries c 9 = ofCoordinates (c 16) (c 17) (c 18) (c 19) (c 20) := rfl

@[simp] theorem highest_0_0 (c : Fin 21 → ℝ) :
    highest c 0 0 = entries c 0 := rfl

@[simp] theorem highest_0_1 (c : Fin 21 → ℝ) :
    highest c 0 1 = entries c 1 := rfl

@[simp] theorem highest_0_2 (c : Fin 21 → ℝ) :
    highest c 0 2 = entries c 2 := rfl

@[simp] theorem highest_0_3 (c : Fin 21 → ℝ) :
    highest c 0 3 = entries c 3 := rfl

@[simp] theorem highest_1_0 (c : Fin 21 → ℝ) :
    highest c 1 0 = entries c 1 := rfl

@[simp] theorem highest_1_1 (c : Fin 21 → ℝ) :
    highest c 1 1 = entries c 4 := rfl

@[simp] theorem highest_1_2 (c : Fin 21 → ℝ) :
    highest c 1 2 = entries c 5 := rfl

@[simp] theorem highest_1_3 (c : Fin 21 → ℝ) :
    highest c 1 3 = entries c 6 := rfl

@[simp] theorem highest_2_0 (c : Fin 21 → ℝ) :
    highest c 2 0 = entries c 2 := rfl

@[simp] theorem highest_2_1 (c : Fin 21 → ℝ) :
    highest c 2 1 = entries c 5 := rfl

@[simp] theorem highest_2_2 (c : Fin 21 → ℝ) :
    highest c 2 2 = entries c 7 := rfl

@[simp] theorem highest_2_3 (c : Fin 21 → ℝ) :
    highest c 2 3 = entries c 8 := rfl

@[simp] theorem highest_3_0 (c : Fin 21 → ℝ) :
    highest c 3 0 = entries c 3 := rfl

@[simp] theorem highest_3_1 (c : Fin 21 → ℝ) :
    highest c 3 1 = entries c 6 := rfl

@[simp] theorem highest_3_2 (c : Fin 21 → ℝ) :
    highest c 3 2 = entries c 8 := rfl

@[simp] theorem highest_3_3 (c : Fin 21 → ℝ) :
    highest c 3 3 = entries c 9 := rfl


def freeCoordinates (c : Fin 50 → ℝ) : Fin 21 → ℝ :=
  ![c 21, c 24, c 26, c 29, c 31, c 34, c 35, c 36, c 37, c 38, c 39, c 40, c 41, c 42, c 43, c 44, c 45, c 46, c 47, c 48, c 49]


@[simp] theorem freeCoordinates_0 (c : Fin 50 → ℝ) :
    freeCoordinates c 0 = c 21 := rfl

@[simp] theorem freeCoordinates_1 (c : Fin 50 → ℝ) :
    freeCoordinates c 1 = c 24 := rfl

@[simp] theorem freeCoordinates_2 (c : Fin 50 → ℝ) :
    freeCoordinates c 2 = c 26 := rfl

@[simp] theorem freeCoordinates_3 (c : Fin 50 → ℝ) :
    freeCoordinates c 3 = c 29 := rfl

@[simp] theorem freeCoordinates_4 (c : Fin 50 → ℝ) :
    freeCoordinates c 4 = c 31 := rfl

@[simp] theorem freeCoordinates_5 (c : Fin 50 → ℝ) :
    freeCoordinates c 5 = c 34 := rfl

@[simp] theorem freeCoordinates_6 (c : Fin 50 → ℝ) :
    freeCoordinates c 6 = c 35 := rfl

@[simp] theorem freeCoordinates_7 (c : Fin 50 → ℝ) :
    freeCoordinates c 7 = c 36 := rfl

@[simp] theorem freeCoordinates_8 (c : Fin 50 → ℝ) :
    freeCoordinates c 8 = c 37 := rfl

@[simp] theorem freeCoordinates_9 (c : Fin 50 → ℝ) :
    freeCoordinates c 9 = c 38 := rfl

@[simp] theorem freeCoordinates_10 (c : Fin 50 → ℝ) :
    freeCoordinates c 10 = c 39 := rfl

@[simp] theorem freeCoordinates_11 (c : Fin 50 → ℝ) :
    freeCoordinates c 11 = c 40 := rfl

@[simp] theorem freeCoordinates_12 (c : Fin 50 → ℝ) :
    freeCoordinates c 12 = c 41 := rfl

@[simp] theorem freeCoordinates_13 (c : Fin 50 → ℝ) :
    freeCoordinates c 13 = c 42 := rfl

@[simp] theorem freeCoordinates_14 (c : Fin 50 → ℝ) :
    freeCoordinates c 14 = c 43 := rfl

@[simp] theorem freeCoordinates_15 (c : Fin 50 → ℝ) :
    freeCoordinates c 15 = c 44 := rfl

@[simp] theorem freeCoordinates_16 (c : Fin 50 → ℝ) :
    freeCoordinates c 16 = c 45 := rfl

@[simp] theorem freeCoordinates_17 (c : Fin 50 → ℝ) :
    freeCoordinates c 17 = c 46 := rfl

@[simp] theorem freeCoordinates_18 (c : Fin 50 → ℝ) :
    freeCoordinates c 18 = c 47 := rfl

@[simp] theorem freeCoordinates_19 (c : Fin 50 → ℝ) :
    freeCoordinates c 19 = c 48 := rfl

@[simp] theorem freeCoordinates_20 (c : Fin 50 → ℝ) :
    freeCoordinates c 20 = c 49 := rfl

/-- Bianchi is imposed on each fixed outer derivative, using the original
quaternion action on the inner derivative and matrix slots. -/
def divergence (X : Hessian) (i : Fin 4) (r : Fin 3) : Vec :=
  ∑ s, quaternion s (WithLp.toLp 2 (fun j => X i j s r))

/-- The highest Hessian tensor is symmetric in its derivatives, has zero
trace, and satisfies the differentiated Bianchi equation. -/
def condition (X : Hessian) : Prop :=
  (∀ i j, X i j = X j i) ∧
  (∀ i j, symmetric (X i j) ∧ traceFree (X i j)) ∧
  hessianTrace X = 0 ∧ ∀ i r, divergence X i r = 0


end
end PositiveEinsteinFour.HighestHessian

end OAI
