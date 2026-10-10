import OAI.Combinatorics.EditApproximation.Binary.BinaryOptimizerSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryReductionSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryBandInputs

namespace OAI

namespace EditApproximation.BinaryFraction

def bandCoordinateAllocation {M : ℕ} {σ : Type*} [DecidableEq σ]
    (mass : Vector BinaryFraction M) (total : BinaryFraction)
    (action : Fin M → σ) (coordinate : Fin M × σ) : ℕ :=
  if coordinate.2 = action coordinate.1 then divAllocation (mass.get coordinate.1) total else 0

def bandCoordinateInvocations {M : ℕ} {σ : Type*} [DecidableEq σ]
    (mass : Vector BinaryFraction M) (total : BinaryFraction)
    (action : Fin M → σ) (coordinate : Fin M × σ) : ℕ :=
  if coordinate.2 = action coordinate.1 then divInvocations (mass.get coordinate.1) total else 1

theorem bandCoordinateAllocation_le_work {M : ℕ} {σ : Type*} [DecidableEq σ]
    (mass : Vector BinaryFraction M) (total : BinaryFraction)
    (action : Fin M → σ) (coordinate : Fin M × σ) :
    bandCoordinateAllocation mass total action coordinate ≤ (bandCoordinateWithWork mass total action coordinate).2 := by
  unfold bandCoordinateAllocation bandCoordinateWithWork
  split_ifs
  · exact divAllocation_le_work _ _
  · exact Nat.zero_le _

theorem bandCoordinateInvocations_le_work {M : ℕ} {σ : Type*} [DecidableEq σ]
    (mass : Vector BinaryFraction M) (total : BinaryFraction)
    (action : Fin M → σ) (coordinate : Fin M × σ) :
    bandCoordinateInvocations mass total action coordinate ≤ (bandCoordinateWithWork mass total action coordinate).2 := by
  unfold bandCoordinateInvocations bandCoordinateWithWork
  split_ifs
  · exact divInvocations_le_work _ _
  · exact le_refl _

def bandVerticesAllocation {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (band : List (Fin M → σ)) : ℕ :=
  bandMassAllocation mass +
    (band.map fun action => vectorMapAllocation d fun i =>
      bandCoordinateAllocation mass (bandMassTotalWithWork mass).1 action (coordinates.get i)).sum +
    3 * band.length

def bandVerticesInvocations {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (band : List (Fin M → σ)) : ℕ :=
  bandMassInvocations mass +
    (band.map fun action => vectorMapInvocations d fun i =>
      bandCoordinateInvocations mass (bandMassTotalWithWork mass).1 action (coordinates.get i)).sum +
    3 * band.length + 1

theorem bandVerticesAllocation_le_work {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (band : List (Fin M → σ)) :
    bandVerticesAllocation coordinates mass band ≤ (bandVerticesWithWork coordinates mass band).2 := by
  have hm := bandMassAllocation_le_work mass
  have hs : (band.map fun action => vectorMapAllocation d fun i =>
      bandCoordinateAllocation mass (bandMassTotalWithWork mass).1 action (coordinates.get i)).sum ≤
      (band.map fun action => (vectorMapWithWork d fun i =>
        bandCoordinateWithWork mass (bandMassTotalWithWork mass).1 action (coordinates.get i)).2).sum := by
    induction band with
    | nil => simp
    | cons a rest ih =>
      have h := vectorMapAllocation_le_work d
        (fun i => bandCoordinateWithWork mass (bandMassTotalWithWork mass).1 a (coordinates.get i))
        (fun i => bandCoordinateAllocation mass (bandMassTotalWithWork mass).1 a (coordinates.get i))
        (fun i => bandCoordinateAllocation_le_work _ _ _ _)
      simp only [List.map_cons, List.sum_cons]
      omega
  unfold bandVerticesAllocation bandVerticesWithWork
  simp only [List.map_map, Function.comp_def]
  omega

theorem bandVerticesInvocations_le_work_add_one {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (band : List (Fin M → σ)) :
    bandVerticesInvocations coordinates mass band ≤ (bandVerticesWithWork coordinates mass band).2 + 1 := by
  have hm := bandMassInvocations_le_work mass
  have hs : (band.map fun action => vectorMapInvocations d fun i =>
      bandCoordinateInvocations mass (bandMassTotalWithWork mass).1 action (coordinates.get i)).sum ≤
      (band.map fun action => (vectorMapWithWork d fun i =>
        bandCoordinateWithWork mass (bandMassTotalWithWork mass).1 action (coordinates.get i)).2).sum + band.length := by
    induction band with
    | nil => simp
    | cons a rest ih =>
      have h := vectorMapInvocations_le_work_add_one d
        (fun i => bandCoordinateWithWork mass (bandMassTotalWithWork mass).1 a (coordinates.get i))
        (fun i => bandCoordinateInvocations mass (bandMassTotalWithWork mass).1 a (coordinates.get i))
        (fun i => bandCoordinateInvocations_le_work _ _ _ _)
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega
  unfold bandVerticesInvocations bandVerticesWithWork
  simp only [List.map_map, Function.comp_def]
  omega

end EditApproximation.BinaryFraction

end OAI
