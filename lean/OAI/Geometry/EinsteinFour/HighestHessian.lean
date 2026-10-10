import OAI.Geometry.EinsteinFour.HighestConstraints

namespace OAI

/-! Every actual highest Hessian has the twenty-one displayed coordinates. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

private theorem entry_reconstruction_0 (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    rawEntries c 0 = entries (freeCoordinates c) 0 := by
  have e0 := (equations_of_constraints c ht hb).pivot_0
  have e1 := (equations_of_constraints c ht hb).pivot_1
  have e2 := (equations_of_constraints c ht hb).pivot_2
  have e3 := (equations_of_constraints c ht hb).pivot_3
  have e4 := (equations_of_constraints c ht hb).pivot_4
  simp only [rawEntries_0, entries_0, e0, e1, e2, e3, e4]

private theorem entry_reconstruction_1 (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    rawEntries c 1 = entries (freeCoordinates c) 1 := by
  have e5 := (equations_of_constraints c ht hb).pivot_5
  have e6 := (equations_of_constraints c ht hb).pivot_6
  have e7 := (equations_of_constraints c ht hb).pivot_7
  have e8 := (equations_of_constraints c ht hb).pivot_8
  have e9 := (equations_of_constraints c ht hb).pivot_9
  simp only [rawEntries_1, entries_1, e5, e6, e7, e8, e9]

private theorem entry_reconstruction_2 (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    rawEntries c 2 = entries (freeCoordinates c) 2 := by
  have e10 := (equations_of_constraints c ht hb).pivot_10
  have e11 := (equations_of_constraints c ht hb).pivot_11
  have e12 := (equations_of_constraints c ht hb).pivot_12
  have e13 := (equations_of_constraints c ht hb).pivot_13
  have e14 := (equations_of_constraints c ht hb).pivot_14
  simp only [rawEntries_2, entries_2, e10, e11, e12, e13, e14]

private theorem entry_reconstruction_3 (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    rawEntries c 3 = entries (freeCoordinates c) 3 := by
  have e15 := (equations_of_constraints c ht hb).pivot_15
  have e16 := (equations_of_constraints c ht hb).pivot_16
  have e17 := (equations_of_constraints c ht hb).pivot_17
  have e18 := (equations_of_constraints c ht hb).pivot_18
  have e19 := (equations_of_constraints c ht hb).pivot_19
  simp only [rawEntries_3, entries_3, e15, e16, e17, e18, e19]

private theorem entry_reconstruction_4 (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    rawEntries c 4 = entries (freeCoordinates c) 4 := by
  have e20 := (equations_of_constraints c ht hb).pivot_20
  have e22 := (equations_of_constraints c ht hb).pivot_22
  have e23 := (equations_of_constraints c ht hb).pivot_23
  simp only [rawEntries_4, entries_4, e20, e22, e23, freeCoordinates_0, freeCoordinates_1]

private theorem entry_reconstruction_5 (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    rawEntries c 5 = entries (freeCoordinates c) 5 := by
  have e25 := (equations_of_constraints c ht hb).pivot_25
  have e27 := (equations_of_constraints c ht hb).pivot_27
  have e28 := (equations_of_constraints c ht hb).pivot_28
  simp only [rawEntries_5, entries_5, e25, e27, e28, freeCoordinates_2, freeCoordinates_3]

private theorem entry_reconstruction_6 (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    rawEntries c 6 = entries (freeCoordinates c) 6 := by
  have e30 := (equations_of_constraints c ht hb).pivot_30
  have e32 := (equations_of_constraints c ht hb).pivot_32
  have e33 := (equations_of_constraints c ht hb).pivot_33
  simp only [rawEntries_6, entries_6, e30, e32, e33, freeCoordinates_4, freeCoordinates_5]

private theorem entry_reconstruction_7 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (_hb : ∀ i r, divergence (raw c) i r = 0) :
    rawEntries c 7 = entries (freeCoordinates c) 7 := by
  simp only [rawEntries_7, entries_7,
    freeCoordinates_6, freeCoordinates_7, freeCoordinates_8, freeCoordinates_9, freeCoordinates_10]

private theorem entry_reconstruction_8 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (_hb : ∀ i r, divergence (raw c) i r = 0) :
    rawEntries c 8 = entries (freeCoordinates c) 8 := by
  simp only [rawEntries_8, entries_8,
    freeCoordinates_11, freeCoordinates_12, freeCoordinates_13, freeCoordinates_14, freeCoordinates_15]

private theorem entry_reconstruction_9 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (_hb : ∀ i r, divergence (raw c) i r = 0) :
    rawEntries c 9 = entries (freeCoordinates c) 9 := by
  simp only [rawEntries_9, entries_9,
    freeCoordinates_16, freeCoordinates_17, freeCoordinates_18, freeCoordinates_19, freeCoordinates_20]

/-- The actual trace and Bianchi constraints determine every nonfree entry. -/
theorem raw_reconstruction (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    raw c = highest (freeCoordinates c) := by
  unfold raw highest
  congr 1
  funext k
  fin_cases k
  · exact entry_reconstruction_0 c ht hb
  · exact entry_reconstruction_1 c ht hb
  · exact entry_reconstruction_2 c ht hb
  · exact entry_reconstruction_3 c ht hb
  · exact entry_reconstruction_4 c ht hb
  · exact entry_reconstruction_5 c ht hb
  · exact entry_reconstruction_6 c ht hb
  · exact entry_reconstruction_7 c ht hb
  · exact entry_reconstruction_8 c ht hb
  · exact entry_reconstruction_9 c ht hb

/-- Extract the fifty independent entries of a derivative-symmetric tensor. -/
def coordinates (X : Hessian) : Fin 50 → ℝ :=
  ![X 0 0 0 0, X 0 0 1 1, X 0 0 0 1, X 0 0 0 2, X 0 0 1 2, X 0 1 0 0, X 0 1 1 1, X 0 1 0 1, X 0 1 0 2, X 0 1 1 2, X 0 2 0 0, X 0 2 1 1, X 0 2 0 1, X 0 2 0 2, X 0 2 1 2, X 0 3 0 0, X 0 3 1 1, X 0 3 0 1, X 0 3 0 2, X 0 3 1 2, X 1 1 0 0, X 1 1 1 1, X 1 1 0 1, X 1 1 0 2, X 1 1 1 2, X 1 2 0 0, X 1 2 1 1, X 1 2 0 1, X 1 2 0 2, X 1 2 1 2, X 1 3 0 0, X 1 3 1 1, X 1 3 0 1, X 1 3 0 2, X 1 3 1 2, X 2 2 0 0, X 2 2 1 1, X 2 2 0 1, X 2 2 0 2, X 2 2 1 2, X 2 3 0 0, X 2 3 1 1, X 2 3 0 1, X 2 3 0 2, X 2 3 1 2, X 3 3 0 0, X 3 3 1 1, X 3 3 0 1, X 3 3 0 2, X 3 3 1 2]


@[simp] theorem coordinates_0 (X : Hessian) :
    coordinates X 0 = X 0 0 0 0 := rfl

@[simp] theorem coordinates_1 (X : Hessian) :
    coordinates X 1 = X 0 0 1 1 := rfl

@[simp] theorem coordinates_2 (X : Hessian) :
    coordinates X 2 = X 0 0 0 1 := rfl

@[simp] theorem coordinates_3 (X : Hessian) :
    coordinates X 3 = X 0 0 0 2 := rfl

@[simp] theorem coordinates_4 (X : Hessian) :
    coordinates X 4 = X 0 0 1 2 := rfl

@[simp] theorem coordinates_5 (X : Hessian) :
    coordinates X 5 = X 0 1 0 0 := rfl

@[simp] theorem coordinates_6 (X : Hessian) :
    coordinates X 6 = X 0 1 1 1 := rfl

@[simp] theorem coordinates_7 (X : Hessian) :
    coordinates X 7 = X 0 1 0 1 := rfl

@[simp] theorem coordinates_8 (X : Hessian) :
    coordinates X 8 = X 0 1 0 2 := rfl

@[simp] theorem coordinates_9 (X : Hessian) :
    coordinates X 9 = X 0 1 1 2 := rfl

@[simp] theorem coordinates_10 (X : Hessian) :
    coordinates X 10 = X 0 2 0 0 := rfl

@[simp] theorem coordinates_11 (X : Hessian) :
    coordinates X 11 = X 0 2 1 1 := rfl

@[simp] theorem coordinates_12 (X : Hessian) :
    coordinates X 12 = X 0 2 0 1 := rfl

@[simp] theorem coordinates_13 (X : Hessian) :
    coordinates X 13 = X 0 2 0 2 := rfl

@[simp] theorem coordinates_14 (X : Hessian) :
    coordinates X 14 = X 0 2 1 2 := rfl

@[simp] theorem coordinates_15 (X : Hessian) :
    coordinates X 15 = X 0 3 0 0 := rfl

@[simp] theorem coordinates_16 (X : Hessian) :
    coordinates X 16 = X 0 3 1 1 := rfl

@[simp] theorem coordinates_17 (X : Hessian) :
    coordinates X 17 = X 0 3 0 1 := rfl

@[simp] theorem coordinates_18 (X : Hessian) :
    coordinates X 18 = X 0 3 0 2 := rfl

@[simp] theorem coordinates_19 (X : Hessian) :
    coordinates X 19 = X 0 3 1 2 := rfl

@[simp] theorem coordinates_20 (X : Hessian) :
    coordinates X 20 = X 1 1 0 0 := rfl

@[simp] theorem coordinates_21 (X : Hessian) :
    coordinates X 21 = X 1 1 1 1 := rfl

@[simp] theorem coordinates_22 (X : Hessian) :
    coordinates X 22 = X 1 1 0 1 := rfl

@[simp] theorem coordinates_23 (X : Hessian) :
    coordinates X 23 = X 1 1 0 2 := rfl

@[simp] theorem coordinates_24 (X : Hessian) :
    coordinates X 24 = X 1 1 1 2 := rfl

@[simp] theorem coordinates_25 (X : Hessian) :
    coordinates X 25 = X 1 2 0 0 := rfl

@[simp] theorem coordinates_26 (X : Hessian) :
    coordinates X 26 = X 1 2 1 1 := rfl

@[simp] theorem coordinates_27 (X : Hessian) :
    coordinates X 27 = X 1 2 0 1 := rfl

@[simp] theorem coordinates_28 (X : Hessian) :
    coordinates X 28 = X 1 2 0 2 := rfl

@[simp] theorem coordinates_29 (X : Hessian) :
    coordinates X 29 = X 1 2 1 2 := rfl

@[simp] theorem coordinates_30 (X : Hessian) :
    coordinates X 30 = X 1 3 0 0 := rfl

@[simp] theorem coordinates_31 (X : Hessian) :
    coordinates X 31 = X 1 3 1 1 := rfl

@[simp] theorem coordinates_32 (X : Hessian) :
    coordinates X 32 = X 1 3 0 1 := rfl

@[simp] theorem coordinates_33 (X : Hessian) :
    coordinates X 33 = X 1 3 0 2 := rfl

@[simp] theorem coordinates_34 (X : Hessian) :
    coordinates X 34 = X 1 3 1 2 := rfl

@[simp] theorem coordinates_35 (X : Hessian) :
    coordinates X 35 = X 2 2 0 0 := rfl

@[simp] theorem coordinates_36 (X : Hessian) :
    coordinates X 36 = X 2 2 1 1 := rfl

@[simp] theorem coordinates_37 (X : Hessian) :
    coordinates X 37 = X 2 2 0 1 := rfl

@[simp] theorem coordinates_38 (X : Hessian) :
    coordinates X 38 = X 2 2 0 2 := rfl

@[simp] theorem coordinates_39 (X : Hessian) :
    coordinates X 39 = X 2 2 1 2 := rfl

@[simp] theorem coordinates_40 (X : Hessian) :
    coordinates X 40 = X 2 3 0 0 := rfl

@[simp] theorem coordinates_41 (X : Hessian) :
    coordinates X 41 = X 2 3 1 1 := rfl

@[simp] theorem coordinates_42 (X : Hessian) :
    coordinates X 42 = X 2 3 0 1 := rfl

@[simp] theorem coordinates_43 (X : Hessian) :
    coordinates X 43 = X 2 3 0 2 := rfl

@[simp] theorem coordinates_44 (X : Hessian) :
    coordinates X 44 = X 2 3 1 2 := rfl

@[simp] theorem coordinates_45 (X : Hessian) :
    coordinates X 45 = X 3 3 0 0 := rfl

@[simp] theorem coordinates_46 (X : Hessian) :
    coordinates X 46 = X 3 3 1 1 := rfl

@[simp] theorem coordinates_47 (X : Hessian) :
    coordinates X 47 = X 3 3 0 1 := rfl

@[simp] theorem coordinates_48 (X : Hessian) :
    coordinates X 48 = X 3 3 0 2 := rfl

@[simp] theorem coordinates_49 (X : Hessian) :
    coordinates X 49 = X 3 3 1 2 := rfl

theorem raw_coordinates (X : Hessian)
    (hs : ∀ i j, X i j = X j i)
    (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j)) :
    raw (coordinates X) = X := by
  funext i j
  fin_cases i <;> fin_cases j
  · simpa using (coordinates_eq (X 0 0) (hm 0 0).1 (hm 0 0).2)
  · simpa using (coordinates_eq (X 0 1) (hm 0 1).1 (hm 0 1).2)
  · simpa using (coordinates_eq (X 0 2) (hm 0 2).1 (hm 0 2).2)
  · simpa using (coordinates_eq (X 0 3) (hm 0 3).1 (hm 0 3).2)
  · simpa using ((coordinates_eq (X 0 1) (hm 0 1).1 (hm 0 1).2).trans (hs 0 1))
  · simpa using (coordinates_eq (X 1 1) (hm 1 1).1 (hm 1 1).2)
  · simpa using (coordinates_eq (X 1 2) (hm 1 2).1 (hm 1 2).2)
  · simpa using (coordinates_eq (X 1 3) (hm 1 3).1 (hm 1 3).2)
  · simpa using ((coordinates_eq (X 0 2) (hm 0 2).1 (hm 0 2).2).trans (hs 0 2))
  · simpa using ((coordinates_eq (X 1 2) (hm 1 2).1 (hm 1 2).2).trans (hs 1 2))
  · simpa using (coordinates_eq (X 2 2) (hm 2 2).1 (hm 2 2).2)
  · simpa using (coordinates_eq (X 2 3) (hm 2 3).1 (hm 2 3).2)
  · simpa using ((coordinates_eq (X 0 3) (hm 0 3).1 (hm 0 3).2).trans (hs 0 3))
  · simpa using ((coordinates_eq (X 1 3) (hm 1 3).1 (hm 1 3).2).trans (hs 1 3))
  · simpa using ((coordinates_eq (X 2 3) (hm 2 3).1 (hm 2 3).2).trans (hs 2 3))
  · simpa using (coordinates_eq (X 3 3) (hm 3 3).1 (hm 3 3).2)

/-- Every actual highest Hessian has the displayed twenty-one coordinates.
Only derivative symmetry, matrix symmetry/trace, and Bianchi are used. -/
theorem exists_highest (X : Hessian) (hX : condition X) :
    ∃ c : Fin 21 → ℝ, highest c = X := by
  obtain ⟨hs, hm, ht, hb⟩ := hX
  have hr := raw_coordinates X hs hm
  refine ⟨freeCoordinates (coordinates X), ?_⟩
  rw [← raw_reconstruction (coordinates X) (by rw [hr]; exact ht)
    (by rw [hr]; exact hb)]
  exact hr

/-- The displayed parameters are independent: extraction recovers each of
 the twenty-one free entries. -/
theorem freeCoordinates_coordinates_highest (c : Fin 21 → ℝ) :
    freeCoordinates (coordinates (highest c)) = c := by
  funext k
  fin_cases k <;> simp [ofCoordinates]

/-- The concrete parameter map has no hidden quotient or redundancy. -/
theorem highest_injective : Function.Injective highest := by
  intro c d h
  have hc := congrArg (fun X => freeCoordinates (coordinates X)) h
  simpa only [freeCoordinates_coordinates_highest] using hc

end
end PositiveEinsteinFour.HighestHessian

end OAI
