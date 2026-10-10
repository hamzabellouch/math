import Mathlib
import OAI.Combinatorics.StripMass.ThreeBoxCertificates

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.ThreeBox
noncomputable section
open Finset

 

def diagram : Fin 51 → Finset (Fin 6 × Fin 6) := ![
  ∅,
  {(0,1)},
  {(0,1),(2,3)},
  {(0,1),(2,3),(4,5)},
  {(0,1),(2,4)},
  {(0,1),(2,5)},
  {(0,1),(2,5),(3,4)},
  {(0,1),(3,4)},
  {(0,1),(3,5)},
  {(0,1),(4,5)},
  {(0,2)},
  {(0,2),(3,4)},
  {(0,2),(3,5)},
  {(0,2),(4,5)},
  {(0,3)},
  {(0,3),(1,2)},
  {(0,3),(1,2),(4,5)},
  {(0,3),(1,4)},
  {(0,3),(1,4),(2,5)},
  {(0,3),(1,5)},
  {(0,3),(2,4)},
  {(0,3),(2,5)},
  {(0,3),(4,5)},
  {(0,4)},
  {(0,4),(1,2)},
  {(0,4),(1,5)},
  {(0,4),(2,5)},
  {(0,5)},
  {(0,5),(1,2)},
  {(0,5),(1,2),(3,4)},
  {(0,5),(3,4)},
  {(1,2)},
  {(1,2),(3,4)},
  {(1,2),(3,5)},
  {(1,2),(4,5)},
  {(1,3)},
  {(1,3),(2,4)},
  {(1,3),(2,5)},
  {(1,3),(4,5)},
  {(1,4)},
  {(1,4),(2,5)},
  {(1,5)},
  {(1,5),(3,4)},
  {(2,3)},
  {(2,3),(4,5)},
  {(2,4)},
  {(2,5)},
  {(2,5),(3,4)},
  {(3,4)},
  {(3,5)},
  {(4,5)}]

def profile : Config → Option (Fin 51)
  | (.vacant,.vacant,.vacant) => some 0
  | (.vacant,.vacant,.cup) => some 50
  | (.vacant,.vertical₀,.vacant) => some 14
  | (.vacant,.vertical₀,.cup) => some 22
  | (.vacant,.diagonal₀,.vertical₀) => some 23
  | (.vacant,.diagonal₀,.diagonal₀) => some 27
  | (.vacant,.cup,.vertical₀) => some 48
  | (.vacant,.cup,.diagonal₀) => some 49
  | (.vertical₀,.vertical₁,.vertical₀) => some 39
  | (.vertical₀,.vertical₁,.diagonal₀) => some 41
  | (.vertical₀,.diagonal₁,.vacant) => some 35
  | (.vertical₀,.diagonal₁,.cup) => some 38
  | (.vertical₀,.cap,.vacant) => some 1
  | (.vertical₀,.cap,.cup) => some 9
  | (.vertical₀,.verticalPair,.vertical₀) => some 17
  | (.vertical₀,.verticalPair,.diagonal₀) => some 19
  | (.vertical₀,.capCup,.vertical₀) => some 7
  | (.vertical₀,.capCup,.diagonal₀) => some 8
  | (.vertical₁,.vacant,.vertical₁) => some 46
  | (.vertical₁,.vacant,.diagonal₁) => some 45
  | (.vertical₁,.vertical₀,.vertical₁) => some 21
  | (.vertical₁,.vertical₀,.diagonal₁) => some 20
  | (.vertical₁,.diagonal₀,.cap) => some 10
  | (.vertical₁,.diagonal₀,.verticalPair) => some 26
  | (.vertical₁,.diagonal₀,.capCup) => some 13
  | (.vertical₁,.cup,.cap) => some 43
  | (.vertical₁,.cup,.verticalPair) => some 47
  | (.vertical₁,.cup,.capCup) => some 44
  | (.diagonal₀,.vacant,.vertical₁) => some 41
  | (.diagonal₀,.vacant,.diagonal₁) => some 39
  | (.diagonal₀,.vertical₀,.vertical₁) => some 19
  | (.diagonal₀,.vertical₀,.diagonal₁) => some 17
  | (.diagonal₀,.diagonal₀,.cap) => some 1
  | (.diagonal₀,.diagonal₀,.verticalPair) => some 25
  | (.diagonal₀,.diagonal₀,.capCup) => some 9
  | (.diagonal₀,.cup,.cap) => some 35
  | (.diagonal₀,.cup,.verticalPair) => some 42
  | (.diagonal₀,.cup,.capCup) => some 38
  | (.diagonal₁,.vertical₁,.vertical₀) => some 45
  | (.diagonal₁,.vertical₁,.diagonal₀) => some 46
  | (.diagonal₁,.diagonal₁,.vacant) => some 43
  | (.diagonal₁,.diagonal₁,.cup) => some 44
  | (.diagonal₁,.cap,.vacant) => some 10
  | (.diagonal₁,.cap,.cup) => some 13
  | (.diagonal₁,.verticalPair,.vertical₀) => some 20
  | (.diagonal₁,.verticalPair,.diagonal₀) => some 21
  | (.diagonal₁,.capCup,.vertical₀) => some 11
  | (.diagonal₁,.capCup,.diagonal₀) => some 12
  | (.cap,.vacant,.vacant) => some 31
  | (.cap,.vacant,.cup) => some 34
  | (.cap,.vertical₀,.vacant) => some 15
  | (.cap,.vertical₀,.cup) => some 16
  | (.cap,.diagonal₀,.vertical₀) => some 24
  | (.cap,.diagonal₀,.diagonal₀) => some 28
  | (.cap,.cup,.vertical₀) => some 32
  | (.cap,.cup,.diagonal₀) => some 33
  | (.cup,.vertical₁,.verticalPair) => some 50
  | (.cup,.diagonal₁,.vertical₁) => some 49
  | (.cup,.diagonal₁,.diagonal₁) => some 48
  | (.cup,.cap,.vertical₁) => some 27
  | (.cup,.cap,.diagonal₁) => some 23
  | (.cup,.verticalPair,.verticalPair) => some 22
  | (.cup,.capCup,.cap) => some 14
  | (.cup,.capCup,.verticalPair) => some 30
  | (.cup,.capCup,.capCup) => some 22
  | (.verticalPair,.vertical₁,.cap) => some 31
  | (.verticalPair,.vertical₁,.verticalPair) => some 40
  | (.verticalPair,.vertical₁,.capCup) => some 34
  | (.verticalPair,.diagonal₁,.vertical₁) => some 37
  | (.verticalPair,.diagonal₁,.diagonal₁) => some 36
  | (.verticalPair,.cap,.vertical₁) => some 5
  | (.verticalPair,.cap,.diagonal₁) => some 4
  | (.verticalPair,.verticalPair,.cap) => some 15
  | (.verticalPair,.verticalPair,.verticalPair) => some 18
  | (.verticalPair,.verticalPair,.capCup) => some 16
  | (.verticalPair,.capCup,.cap) => some 2
  | (.verticalPair,.capCup,.verticalPair) => some 6
  | (.verticalPair,.capCup,.capCup) => some 3
  | (.capCup,.vertical₁,.verticalPair) => some 34
  | (.capCup,.diagonal₁,.vertical₁) => some 33
  | (.capCup,.diagonal₁,.diagonal₁) => some 32
  | (.capCup,.cap,.vertical₁) => some 28
  | (.capCup,.cap,.diagonal₁) => some 24
  | (.capCup,.verticalPair,.verticalPair) => some 16
  | (.capCup,.capCup,.cap) => some 15
  | (.capCup,.capCup,.verticalPair) => some 29
  | (.capCup,.capCup,.capCup) => some 16
  | _ => none

def Clean (t : Config) : Prop :=
  ∀ v w, Adj t v w → ∃ i, boundaryOccupied t i ∧ rootTable t v = rootTable t (boundary i)

def BoundaryData (t : Config) (d : Finset (Fin 6 × Fin 6)) : Prop :=
  (∀ i, boundaryOccupied t i ↔ boundarySupport d i) ∧
  (∀ i j, i ≠ j → (boundaryAdj d i j ↔ rootTable t (boundary i) = rootTable t (boundary j)))

instance cleanDecidable (t : Config) : Decidable (Clean t) := by
  unfold Clean; infer_instance
instance boundaryAdjDecidable (d : Finset (Fin 6 × Fin 6)) (i j : Fin 6) :
    Decidable (boundaryAdj d i j) := by unfold boundaryAdj; infer_instance
instance boundarySupportDecidable (d : Finset (Fin 6 × Fin 6)) (i : Fin 6) :
    Decidable (boundarySupport d i) := by unfold boundarySupport; infer_instance
instance boundaryDataDecidable (t : Config) (d : Finset (Fin 6 × Fin 6)) :
    Decidable (BoundaryData t d) := by unfold BoundaryData; infer_instance

def ProfileCorrect (t : Config) : Prop :=
  match profile t with
  | none => ¬ Compatible t ∨ ¬ Clean t
  | some k => Compatible t ∧ Clean t ∧ BoundaryData t (diagram k)
instance profileCorrectDecidable (t : Config) : Decidable (ProfileCorrect t) := by
  unfold ProfileCorrect; split <;> infer_instance

theorem profileCorrect_0 (x y : Tile) : ProfileCorrect (.vacant,x,y) := by
  cases x <;> cases y <;> decide

theorem profileCorrect_1 (x y : Tile) : ProfileCorrect (.vertical₀,x,y) := by
  cases x <;> cases y <;> decide

theorem profileCorrect_2 (x y : Tile) : ProfileCorrect (.vertical₁,x,y) := by
  cases x <;> cases y <;> decide

theorem profileCorrect_3 (x y : Tile) : ProfileCorrect (.diagonal₀,x,y) := by
  cases x <;> cases y <;> decide

theorem profileCorrect_4 (x y : Tile) : ProfileCorrect (.diagonal₁,x,y) := by
  cases x <;> cases y <;> decide

theorem profileCorrect_5 (x y : Tile) : ProfileCorrect (.cap,x,y) := by
  cases x <;> cases y <;> decide

theorem profileCorrect_6 (x y : Tile) : ProfileCorrect (.cup,x,y) := by
  cases x <;> cases y <;> decide

theorem profileCorrect_7 (x y : Tile) : ProfileCorrect (.verticalPair,x,y) := by
  cases x <;> cases y <;> decide

theorem profileCorrect_8 (x y : Tile) : ProfileCorrect (.capCup,x,y) := by
  cases x <;> cases y <;> decide

theorem profileCorrect (t : Config) : ProfileCorrect t := by
  rcases t with ⟨t,x,y⟩
  cases t
  · exact profileCorrect_0 x y
  · exact profileCorrect_1 x y
  · exact profileCorrect_2 x y
  · exact profileCorrect_3 x y
  · exact profileCorrect_4 x y
  · exact profileCorrect_5 x y
  · exact profileCorrect_6 x y
  · exact profileCorrect_7 x y
  · exact profileCorrect_8 x y

theorem diagram_injective : Function.Injective diagram := by decide

theorem diagram_upper (k : Fin 51) : ∀ e ∈ diagram k, e.1 < e.2 := by
  fin_cases k <;> decide

theorem realizes_iff_conditions {t : Config} {d : Finset (Fin 6 × Fin 6)} :
    Realizes t d ↔ Compatible t ∧ Clean t ∧ BoundaryData t d := by
  constructor
  · intro h
    refine ⟨h.compatible, ?_, h.occupied, ?_⟩
    · intro v w he
      obtain ⟨i,hi,hr⟩ := h.no_loop v w he
      exact ⟨i,hi,(reach_iff_root_eq t h.compatible v (boundary i)).mp hr⟩
    · intro i j hij
      exact (h.output i j hij).trans (reach_iff_root_eq t h.compatible _ _)
  · rintro ⟨hc,hl,ho,he⟩
    refine ⟨hc,ho,?_,?_⟩
    · intro v w hvw
      obtain ⟨i,hi,hr⟩ := hl v w hvw
      exact ⟨i,hi,(reach_iff_root_eq t hc v (boundary i)).mpr hr⟩
    · intro i j hij
      exact (he i j hij).trans (reach_iff_root_eq t hc _ _).symm

theorem realizes_unique {t : Config} {i j : Fin 51}
    (hi : Realizes t (diagram i)) (hj : Realizes t (diagram j)) : i = j := by
  apply diagram_injective
  have hadj : ∀ a b, a ≠ b → (boundaryAdj (diagram i) a b ↔ boundaryAdj (diagram j) a b) :=
    fun a b hab => (hi.output a b hab).trans (hj.output a b hab).symm
  apply Finset.ext
  intro e
  constructor
  · intro he
    have hu := diagram_upper i e he
    have hh := (hadj e.1 e.2 (ne_of_lt hu)).mp (Or.inl he)
    rcases hh with he' | he'
    · exact he'
    · exact (lt_asymm hu (diagram_upper j _ he')).elim
  · intro he
    have hu := diagram_upper j e he
    have hh := (hadj e.1 e.2 (ne_of_lt hu)).mpr (Or.inl he)
    rcases hh with he' | he'
    · exact he'
    · exact (lt_asymm hu (diagram_upper i _ he')).elim

 

theorem profile_some_iff {t : Config} {k : Fin 51} :
    profile t = some k ↔ Realizes t (diagram k) := by
  have ht := profileCorrect t
  unfold ProfileCorrect at ht
  constructor
  · intro h
    rw [h] at ht
    exact realizes_iff_conditions.mpr ht
  · intro h
    cases he : profile t with
    | none =>
      rw [he] at ht
      obtain ⟨hc,hl,_⟩ := realizes_iff_conditions.mp h
      exact (ht.elim (fun hh => hh hc) (fun hh => hh hl)).elim
    | some j =>
      rw [he] at ht
      have hj := realizes_iff_conditions.mpr ht
      rw [realizes_unique hj h]

end
end CriticalStrip.Diagram.ThreeBox

end OAI
