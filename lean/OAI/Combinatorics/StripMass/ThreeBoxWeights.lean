import Mathlib
import OAI.Combinatorics.StripMass.ThreeBoxProfiles

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.ThreeBox
noncomputable section
open Finset
open scoped Classical

def fiber : Fin 51 → Finset Config := ![
  {(.vacant,.vacant,.vacant)},
  {(.vertical₀,.cap,.vacant),(.diagonal₀,.diagonal₀,.cap)},
  {(.verticalPair,.capCup,.cap)},
  {(.verticalPair,.capCup,.capCup)},
  {(.verticalPair,.cap,.diagonal₁)},
  {(.verticalPair,.cap,.vertical₁)},
  {(.verticalPair,.capCup,.verticalPair)},
  {(.vertical₀,.capCup,.vertical₀)},
  {(.vertical₀,.capCup,.diagonal₀)},
  {(.vertical₀,.cap,.cup),(.diagonal₀,.diagonal₀,.capCup)},
  {(.vertical₁,.diagonal₀,.cap),(.diagonal₁,.cap,.vacant)},
  {(.diagonal₁,.capCup,.vertical₀)},
  {(.diagonal₁,.capCup,.diagonal₀)},
  {(.vertical₁,.diagonal₀,.capCup),(.diagonal₁,.cap,.cup)},
  {(.vacant,.vertical₀,.vacant),(.cup,.capCup,.cap)},
  {(.cap,.vertical₀,.vacant),(.verticalPair,.verticalPair,.cap),(.capCup,.capCup,.cap)},
  {(.cap,.vertical₀,.cup),(.verticalPair,.verticalPair,.capCup),(.capCup,.verticalPair,.verticalPair),(.capCup,.capCup,.capCup)},
  {(.vertical₀,.verticalPair,.vertical₀),(.diagonal₀,.vertical₀,.diagonal₁)},
  {(.verticalPair,.verticalPair,.verticalPair)},
  {(.vertical₀,.verticalPair,.diagonal₀),(.diagonal₀,.vertical₀,.vertical₁)},
  {(.vertical₁,.vertical₀,.diagonal₁),(.diagonal₁,.verticalPair,.vertical₀)},
  {(.vertical₁,.vertical₀,.vertical₁),(.diagonal₁,.verticalPair,.diagonal₀)},
  {(.vacant,.vertical₀,.cup),(.cup,.verticalPair,.verticalPair),(.cup,.capCup,.capCup)},
  {(.vacant,.diagonal₀,.vertical₀),(.cup,.cap,.diagonal₁)},
  {(.cap,.diagonal₀,.vertical₀),(.capCup,.cap,.diagonal₁)},
  {(.diagonal₀,.diagonal₀,.verticalPair)},
  {(.vertical₁,.diagonal₀,.verticalPair)},
  {(.vacant,.diagonal₀,.diagonal₀),(.cup,.cap,.vertical₁)},
  {(.cap,.diagonal₀,.diagonal₀),(.capCup,.cap,.vertical₁)},
  {(.capCup,.capCup,.verticalPair)},
  {(.cup,.capCup,.verticalPair)},
  {(.cap,.vacant,.vacant),(.verticalPair,.vertical₁,.cap)},
  {(.cap,.cup,.vertical₀),(.capCup,.diagonal₁,.diagonal₁)},
  {(.cap,.cup,.diagonal₀),(.capCup,.diagonal₁,.vertical₁)},
  {(.cap,.vacant,.cup),(.verticalPair,.vertical₁,.capCup),(.capCup,.vertical₁,.verticalPair)},
  {(.vertical₀,.diagonal₁,.vacant),(.diagonal₀,.cup,.cap)},
  {(.verticalPair,.diagonal₁,.diagonal₁)},
  {(.verticalPair,.diagonal₁,.vertical₁)},
  {(.vertical₀,.diagonal₁,.cup),(.diagonal₀,.cup,.capCup)},
  {(.vertical₀,.vertical₁,.vertical₀),(.diagonal₀,.vacant,.diagonal₁)},
  {(.verticalPair,.vertical₁,.verticalPair)},
  {(.vertical₀,.vertical₁,.diagonal₀),(.diagonal₀,.vacant,.vertical₁)},
  {(.diagonal₀,.cup,.verticalPair)},
  {(.vertical₁,.cup,.cap),(.diagonal₁,.diagonal₁,.vacant)},
  {(.vertical₁,.cup,.capCup),(.diagonal₁,.diagonal₁,.cup)},
  {(.vertical₁,.vacant,.diagonal₁),(.diagonal₁,.vertical₁,.vertical₀)},
  {(.vertical₁,.vacant,.vertical₁),(.diagonal₁,.vertical₁,.diagonal₀)},
  {(.vertical₁,.cup,.verticalPair)},
  {(.vacant,.cup,.vertical₀),(.cup,.diagonal₁,.diagonal₁)},
  {(.vacant,.cup,.diagonal₀),(.cup,.diagonal₁,.vertical₁)},
  {(.vacant,.vacant,.cup),(.cup,.vertical₁,.verticalPair)}]

theorem fiber_correct_0 : ∀ t : Config, t ∈ fiber 0 ↔ profile t = some 0 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_1 : ∀ t : Config, t ∈ fiber 1 ↔ profile t = some 1 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_2 : ∀ t : Config, t ∈ fiber 2 ↔ profile t = some 2 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_3 : ∀ t : Config, t ∈ fiber 3 ↔ profile t = some 3 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_4 : ∀ t : Config, t ∈ fiber 4 ↔ profile t = some 4 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_5 : ∀ t : Config, t ∈ fiber 5 ↔ profile t = some 5 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_6 : ∀ t : Config, t ∈ fiber 6 ↔ profile t = some 6 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_7 : ∀ t : Config, t ∈ fiber 7 ↔ profile t = some 7 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_8 : ∀ t : Config, t ∈ fiber 8 ↔ profile t = some 8 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_9 : ∀ t : Config, t ∈ fiber 9 ↔ profile t = some 9 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_10 : ∀ t : Config, t ∈ fiber 10 ↔ profile t = some 10 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_11 : ∀ t : Config, t ∈ fiber 11 ↔ profile t = some 11 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_12 : ∀ t : Config, t ∈ fiber 12 ↔ profile t = some 12 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_13 : ∀ t : Config, t ∈ fiber 13 ↔ profile t = some 13 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_14 : ∀ t : Config, t ∈ fiber 14 ↔ profile t = some 14 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_15 : ∀ t : Config, t ∈ fiber 15 ↔ profile t = some 15 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_16 : ∀ t : Config, t ∈ fiber 16 ↔ profile t = some 16 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_17 : ∀ t : Config, t ∈ fiber 17 ↔ profile t = some 17 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_18 : ∀ t : Config, t ∈ fiber 18 ↔ profile t = some 18 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_19 : ∀ t : Config, t ∈ fiber 19 ↔ profile t = some 19 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_20 : ∀ t : Config, t ∈ fiber 20 ↔ profile t = some 20 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_21 : ∀ t : Config, t ∈ fiber 21 ↔ profile t = some 21 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_22 : ∀ t : Config, t ∈ fiber 22 ↔ profile t = some 22 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_23 : ∀ t : Config, t ∈ fiber 23 ↔ profile t = some 23 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_24 : ∀ t : Config, t ∈ fiber 24 ↔ profile t = some 24 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_25 : ∀ t : Config, t ∈ fiber 25 ↔ profile t = some 25 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_26 : ∀ t : Config, t ∈ fiber 26 ↔ profile t = some 26 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_27 : ∀ t : Config, t ∈ fiber 27 ↔ profile t = some 27 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_28 : ∀ t : Config, t ∈ fiber 28 ↔ profile t = some 28 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_29 : ∀ t : Config, t ∈ fiber 29 ↔ profile t = some 29 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_30 : ∀ t : Config, t ∈ fiber 30 ↔ profile t = some 30 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_31 : ∀ t : Config, t ∈ fiber 31 ↔ profile t = some 31 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_32 : ∀ t : Config, t ∈ fiber 32 ↔ profile t = some 32 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_33 : ∀ t : Config, t ∈ fiber 33 ↔ profile t = some 33 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_34 : ∀ t : Config, t ∈ fiber 34 ↔ profile t = some 34 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_35 : ∀ t : Config, t ∈ fiber 35 ↔ profile t = some 35 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_36 : ∀ t : Config, t ∈ fiber 36 ↔ profile t = some 36 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_37 : ∀ t : Config, t ∈ fiber 37 ↔ profile t = some 37 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_38 : ∀ t : Config, t ∈ fiber 38 ↔ profile t = some 38 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_39 : ∀ t : Config, t ∈ fiber 39 ↔ profile t = some 39 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_40 : ∀ t : Config, t ∈ fiber 40 ↔ profile t = some 40 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_41 : ∀ t : Config, t ∈ fiber 41 ↔ profile t = some 41 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_42 : ∀ t : Config, t ∈ fiber 42 ↔ profile t = some 42 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_43 : ∀ t : Config, t ∈ fiber 43 ↔ profile t = some 43 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_44 : ∀ t : Config, t ∈ fiber 44 ↔ profile t = some 44 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_45 : ∀ t : Config, t ∈ fiber 45 ↔ profile t = some 45 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_46 : ∀ t : Config, t ∈ fiber 46 ↔ profile t = some 46 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_47 : ∀ t : Config, t ∈ fiber 47 ↔ profile t = some 47 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_48 : ∀ t : Config, t ∈ fiber 48 ↔ profile t = some 48 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_49 : ∀ t : Config, t ∈ fiber 49 ↔ profile t = some 49 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_50 : ∀ t : Config, t ∈ fiber 50 ↔ profile t = some 50 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem mem_fiber_iff (k : Fin 51) (t : Config) : t ∈ fiber k ↔ profile t = some k := by
  fin_cases k
  · exact fiber_correct_0 t
  · exact fiber_correct_1 t
  · exact fiber_correct_2 t
  · exact fiber_correct_3 t
  · exact fiber_correct_4 t
  · exact fiber_correct_5 t
  · exact fiber_correct_6 t
  · exact fiber_correct_7 t
  · exact fiber_correct_8 t
  · exact fiber_correct_9 t
  · exact fiber_correct_10 t
  · exact fiber_correct_11 t
  · exact fiber_correct_12 t
  · exact fiber_correct_13 t
  · exact fiber_correct_14 t
  · exact fiber_correct_15 t
  · exact fiber_correct_16 t
  · exact fiber_correct_17 t
  · exact fiber_correct_18 t
  · exact fiber_correct_19 t
  · exact fiber_correct_20 t
  · exact fiber_correct_21 t
  · exact fiber_correct_22 t
  · exact fiber_correct_23 t
  · exact fiber_correct_24 t
  · exact fiber_correct_25 t
  · exact fiber_correct_26 t
  · exact fiber_correct_27 t
  · exact fiber_correct_28 t
  · exact fiber_correct_29 t
  · exact fiber_correct_30 t
  · exact fiber_correct_31 t
  · exact fiber_correct_32 t
  · exact fiber_correct_33 t
  · exact fiber_correct_34 t
  · exact fiber_correct_35 t
  · exact fiber_correct_36 t
  · exact fiber_correct_37 t
  · exact fiber_correct_38 t
  · exact fiber_correct_39 t
  · exact fiber_correct_40 t
  · exact fiber_correct_41 t
  · exact fiber_correct_42 t
  · exact fiber_correct_43 t
  · exact fiber_correct_44 t
  · exact fiber_correct_45 t
  · exact fiber_correct_46 t
  · exact fiber_correct_47 t
  · exact fiber_correct_48 t
  · exact fiber_correct_49 t
  · exact fiber_correct_50 t

def coefficient {K : Type*} [CommSemiring K] (a b c : Tile → K) (k : Fin 51) : K :=
  ∑ t ∈ fiber k, a t.1 * b t.2.1 * c t.2.2

def literalCoefficient {K : Type*} [CommSemiring K] (a b c : Tile → K)
    (d : Finset (Fin 6 × Fin 6)) : K :=
  ∑ t : Config, if Realizes t d then a t.1 * b t.2.1 * c t.2.2 else 0

theorem coefficient_eq_literal {K : Type*} [CommSemiring K] (a b c : Tile → K) (k : Fin 51) :
    coefficient a b c k = literalCoefficient a b c (diagram k) := by
  unfold coefficient literalCoefficient
  rw [← Finset.sum_filter]
  congr 1
  ext t
  simp only [mem_filter, mem_univ, true_and, mem_fiber_iff, profile_some_iff]

def mirrorIndex : Fin 51 → Fin 51 := ![0,31,28,29,24,15,16,34,33,32,10,13,12,11,46,5,6,40,18,37,26,21,47,45,4,36,20,43,2,3,44,1,9,8,7,41,25,19,42,39,17,35,38,27,30,23,14,22,50,49,48]

theorem mirrorIndex_involutive : Function.Involutive mirrorIndex := by
  unfold Function.Involutive
  decide

def reverseSlots : Fin 6 → Fin 6 := ![2,1,0,5,4,3]

theorem diagram_mirror (k : Fin 51) (i j : Fin 6) :
    boundaryAdj (diagram (mirrorIndex k)) i j ↔
      boundaryAdj (diagram k) (reverseSlots i) (reverseSlots j) := by
  fin_cases k <;> decide +revert

 

def tileNumerator {K : Type*} [CommRing K] (q I z : K) : Tile → K
  | .vacant => (q^4*z^2-1)*(q^6*z^2-1)
  | .vertical₀ | .vertical₁ => I*(q^4+1)*z*(q^6-z^2)
  | .diagonal₀ | .diagonal₁ => q^2*(z^2-1)*(q^6-z^2)
  | .cap | .cup => I*(q^4+1)*q^3*z*(z^2-1)
  | .verticalPair => (q^6-z^2)*(q^4-z^2)
  | .capCup => q^4*(z^2-q^2)*(z^2-1)

theorem coefficient_0 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 0 = a .vacant * b .vacant * c .vacant := by
  simp [coefficient, fiber]

theorem coefficient_1 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 1 = a .vertical₀ * b .cap * c .vacant + a .diagonal₀ * b .diagonal₀ * c .cap := by
  simp [coefficient, fiber]

theorem coefficient_2 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 2 = a .verticalPair * b .capCup * c .cap := by
  simp [coefficient, fiber]

theorem coefficient_3 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 3 = a .verticalPair * b .capCup * c .capCup := by
  simp [coefficient, fiber]

theorem coefficient_4 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 4 = a .verticalPair * b .cap * c .diagonal₁ := by
  simp [coefficient, fiber]

theorem coefficient_5 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 5 = a .verticalPair * b .cap * c .vertical₁ := by
  simp [coefficient, fiber]

theorem coefficient_6 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 6 = a .verticalPair * b .capCup * c .verticalPair := by
  simp [coefficient, fiber]

theorem coefficient_7 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 7 = a .vertical₀ * b .capCup * c .vertical₀ := by
  simp [coefficient, fiber]

theorem coefficient_8 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 8 = a .vertical₀ * b .capCup * c .diagonal₀ := by
  simp [coefficient, fiber]

theorem coefficient_9 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 9 = a .vertical₀ * b .cap * c .cup + a .diagonal₀ * b .diagonal₀ * c .capCup := by
  simp [coefficient, fiber]

theorem coefficient_10 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 10 = a .vertical₁ * b .diagonal₀ * c .cap + a .diagonal₁ * b .cap * c .vacant := by
  simp [coefficient, fiber]

theorem coefficient_11 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 11 = a .diagonal₁ * b .capCup * c .vertical₀ := by
  simp [coefficient, fiber]

theorem coefficient_12 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 12 = a .diagonal₁ * b .capCup * c .diagonal₀ := by
  simp [coefficient, fiber]

theorem coefficient_13 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 13 = a .vertical₁ * b .diagonal₀ * c .capCup + a .diagonal₁ * b .cap * c .cup := by
  simp [coefficient, fiber]

theorem coefficient_14 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 14 = a .vacant * b .vertical₀ * c .vacant + a .cup * b .capCup * c .cap := by
  simp [coefficient, fiber]

theorem coefficient_15 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 15 = a .cap * b .vertical₀ * c .vacant + a .verticalPair * b .verticalPair * c .cap + a .capCup * b .capCup * c .cap := by
  simp [coefficient, fiber, add_assoc]

theorem coefficient_16 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 16 = a .cap * b .vertical₀ * c .cup + a .verticalPair * b .verticalPair * c .capCup + a .capCup * b .verticalPair * c .verticalPair + a .capCup * b .capCup * c .capCup := by
  simp [coefficient, fiber, add_assoc]

theorem coefficient_17 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 17 = a .vertical₀ * b .verticalPair * c .vertical₀ + a .diagonal₀ * b .vertical₀ * c .diagonal₁ := by
  simp [coefficient, fiber]

theorem coefficient_18 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 18 = a .verticalPair * b .verticalPair * c .verticalPair := by
  simp [coefficient, fiber]

theorem coefficient_19 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 19 = a .vertical₀ * b .verticalPair * c .diagonal₀ + a .diagonal₀ * b .vertical₀ * c .vertical₁ := by
  simp [coefficient, fiber]

theorem coefficient_20 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 20 = a .vertical₁ * b .vertical₀ * c .diagonal₁ + a .diagonal₁ * b .verticalPair * c .vertical₀ := by
  simp [coefficient, fiber]

theorem coefficient_21 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 21 = a .vertical₁ * b .vertical₀ * c .vertical₁ + a .diagonal₁ * b .verticalPair * c .diagonal₀ := by
  simp [coefficient, fiber]

theorem coefficient_22 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 22 = a .vacant * b .vertical₀ * c .cup + a .cup * b .verticalPair * c .verticalPair + a .cup * b .capCup * c .capCup := by
  simp [coefficient, fiber, add_assoc]

theorem coefficient_23 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 23 = a .vacant * b .diagonal₀ * c .vertical₀ + a .cup * b .cap * c .diagonal₁ := by
  simp [coefficient, fiber]

theorem coefficient_24 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 24 = a .cap * b .diagonal₀ * c .vertical₀ + a .capCup * b .cap * c .diagonal₁ := by
  simp [coefficient, fiber]

theorem coefficient_25 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 25 = a .diagonal₀ * b .diagonal₀ * c .verticalPair := by
  simp [coefficient, fiber]

theorem coefficient_26 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 26 = a .vertical₁ * b .diagonal₀ * c .verticalPair := by
  simp [coefficient, fiber]

theorem coefficient_27 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 27 = a .vacant * b .diagonal₀ * c .diagonal₀ + a .cup * b .cap * c .vertical₁ := by
  simp [coefficient, fiber]

theorem coefficient_28 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 28 = a .cap * b .diagonal₀ * c .diagonal₀ + a .capCup * b .cap * c .vertical₁ := by
  simp [coefficient, fiber]

theorem coefficient_29 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 29 = a .capCup * b .capCup * c .verticalPair := by
  simp [coefficient, fiber]

theorem coefficient_30 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 30 = a .cup * b .capCup * c .verticalPair := by
  simp [coefficient, fiber]

theorem coefficient_31 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 31 = a .cap * b .vacant * c .vacant + a .verticalPair * b .vertical₁ * c .cap := by
  simp [coefficient, fiber]

theorem coefficient_32 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 32 = a .cap * b .cup * c .vertical₀ + a .capCup * b .diagonal₁ * c .diagonal₁ := by
  simp [coefficient, fiber]

theorem coefficient_33 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 33 = a .cap * b .cup * c .diagonal₀ + a .capCup * b .diagonal₁ * c .vertical₁ := by
  simp [coefficient, fiber]

theorem coefficient_34 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 34 = a .cap * b .vacant * c .cup + a .verticalPair * b .vertical₁ * c .capCup + a .capCup * b .vertical₁ * c .verticalPair := by
  simp [coefficient, fiber, add_assoc]

theorem coefficient_35 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 35 = a .vertical₀ * b .diagonal₁ * c .vacant + a .diagonal₀ * b .cup * c .cap := by
  simp [coefficient, fiber]

theorem coefficient_36 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 36 = a .verticalPair * b .diagonal₁ * c .diagonal₁ := by
  simp [coefficient, fiber]

theorem coefficient_37 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 37 = a .verticalPair * b .diagonal₁ * c .vertical₁ := by
  simp [coefficient, fiber]

theorem coefficient_38 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 38 = a .vertical₀ * b .diagonal₁ * c .cup + a .diagonal₀ * b .cup * c .capCup := by
  simp [coefficient, fiber]

theorem coefficient_39 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 39 = a .vertical₀ * b .vertical₁ * c .vertical₀ + a .diagonal₀ * b .vacant * c .diagonal₁ := by
  simp [coefficient, fiber]

theorem coefficient_40 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 40 = a .verticalPair * b .vertical₁ * c .verticalPair := by
  simp [coefficient, fiber]

theorem coefficient_41 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 41 = a .vertical₀ * b .vertical₁ * c .diagonal₀ + a .diagonal₀ * b .vacant * c .vertical₁ := by
  simp [coefficient, fiber]

theorem coefficient_42 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 42 = a .diagonal₀ * b .cup * c .verticalPair := by
  simp [coefficient, fiber]

theorem coefficient_43 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 43 = a .vertical₁ * b .cup * c .cap + a .diagonal₁ * b .diagonal₁ * c .vacant := by
  simp [coefficient, fiber]

theorem coefficient_44 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 44 = a .vertical₁ * b .cup * c .capCup + a .diagonal₁ * b .diagonal₁ * c .cup := by
  simp [coefficient, fiber]

theorem coefficient_45 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 45 = a .vertical₁ * b .vacant * c .diagonal₁ + a .diagonal₁ * b .vertical₁ * c .vertical₀ := by
  simp [coefficient, fiber]

theorem coefficient_46 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 46 = a .vertical₁ * b .vacant * c .vertical₁ + a .diagonal₁ * b .vertical₁ * c .diagonal₀ := by
  simp [coefficient, fiber]

theorem coefficient_47 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 47 = a .vertical₁ * b .cup * c .verticalPair := by
  simp [coefficient, fiber]

theorem coefficient_48 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 48 = a .vacant * b .cup * c .vertical₀ + a .cup * b .diagonal₁ * c .diagonal₁ := by
  simp [coefficient, fiber]

theorem coefficient_49 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 49 = a .vacant * b .cup * c .diagonal₀ + a .cup * b .diagonal₁ * c .vertical₁ := by
  simp [coefficient, fiber]

theorem coefficient_50 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 50 = a .vacant * b .vacant * c .cup + a .cup * b .vertical₁ * c .verticalPair := by
  simp [coefficient, fiber]

end
end CriticalStrip.Diagram.ThreeBox

end OAI
