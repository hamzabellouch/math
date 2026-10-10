import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkDiagramParametersDecode
import OAI.NumberTheory.Ostmann.Conclusion.BulkPositionPermutation
import OAI.NumberTheory.Ostmann.Construction.ActualAmplitude

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkDiagramParameters
open Construction Conclusion HistoryTreeParameters HistoryResidueRegular
  HistorySignedSpectatorDiagram
variable {q : ℕ} [Fact q.Prime]

theorem parameters_outer_eq (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (giant : PrimeSource)
    (x y : OuterSample sources (Template.current seed l) giant) (s : ℤ)
    (c : HistoryChoices sources seed V l)
    (hxy : ∀i : Fin (Template.current seed l).length,
      (Template.current seed l)[i].role≠.bulk → (x.2.2 i:ℕ)=(y.2.2 i:ℕ))
    (hx : (decodeHistory sources seed V l
      (outerState sources (Template.current seed l) giant x s) c).Supported V outside)
    (hy : (decodeHistory sources seed V l
      (outerState sources (Template.current seed l) giant y s) c).Supported V outside)
    (hrx : Regular q (decodeHistory sources seed V l
      (outerState sources (Template.current seed l) giant x s) c))
    (hry : Regular q (decodeHistory sources seed V l
      (outerState sources (Template.current seed l) giant y s) c)) (sign : Bool) :
    parameters V outside (decodeHistory sources seed V l
      (outerState sources (Template.current seed l) giant x s) c) hx hrx sign=
    parameters V outside (decodeHistory sources seed V l
      (outerState sources (Template.current seed l) giant y s) c) hy hry sign := by
  apply parameters_decode_eq
  · rfl
  · exact assignedSlots_erase_eq sources (Template.current seed l) x.2.2 y.2.2 hxy

theorem assignedSlots_leafBulkPermutation_erase_eq (b k l : ℕ) (bulk : PrimeSource)
    (top : Fin 3→PrimeSource) (comp : Fin k→Fin 2→PrimeSource)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*b)))
    (x : SourceAssignment (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l)) :
    (assignedSlots (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l)
      (leafBulkAssignmentPermutation b k l bulk top comp σ x)).map eraseBulkValue=
    (assignedSlots (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l) x).map eraseBulkValue := by
  apply assignedSlots_erase_eq
  intro i hi
  rw [leafBulkAssignmentPermutation_val,leafBulkPermutation_apply_nonbulk _ _ _ _ _ hi]

theorem parameters_leafBulkPermutation (b k l : ℕ) (bulk : PrimeSource)
    (top : Fin 3→PrimeSource) (comp : Fin k→Fin 2→PrimeSource)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*b)))
    (V : ℕ→ℕ) (outside : List ℕ)
    (x : SourceAssignment (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l))
    (s : ℤ) (Gp Gm Gp' Gm' : ℕ)
    (c : HistoryChoices (initialSourceFamily b k bulk top comp) (Template.initial (2*b) k) V l) :
    let sources := initialSourceFamily b k bulk top comp
    let seed := Template.initial (2*b) k
    let T := Template.current seed l
    let a : State := ⟨s,Gp,Gm,assignedSlots sources T x⟩
    let a' : State := ⟨s,Gp',Gm',assignedSlots sources T
      (leafBulkAssignmentPermutation b k l bulk top comp σ x)⟩
    ∀(ha : (decodeHistory sources seed V l a c).Supported V outside)
      (ha' : (decodeHistory sources seed V l a' c).Supported V outside)
      (hr : Regular q (decodeHistory sources seed V l a c))
      (hr' : Regular q (decodeHistory sources seed V l a' c)) (sign : Bool),
      parameters V outside (decodeHistory sources seed V l a' c) ha' hr' sign=
        parameters V outside (decodeHistory sources seed V l a c) ha hr sign := by
  dsimp only
  intro ha ha' hr hr' sign
  apply parameters_decode_eq
  · rfl
  · exact assignedSlots_leafBulkPermutation_erase_eq b k l bulk top comp σ x

end Ostmann.Arithmetic.HistoryBulkDiagramParameters

end

end OAI
