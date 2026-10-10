import OAI.Combinatorics.ContingencyTables.Sampling.SmallRepairWords

namespace OAI

/-! # Explicit arithmetic inverse of each labelled repair -/

namespace ContingencyTables.SmallGraphProfiles

open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles

noncomputable section
universe u
variable {I J : Type u} [LinearOrder I] [LinearOrder J]

/-- Undo the row transfer, using only additions, subtractions and tests
against the two specified cells. -/
def inverseRepairRow (small : I → J → Bool) (v : SmallProfile small) (s t : I×J)
    (i : I) (j : J) : ℕ :=
  (transferInt (smallView small v false) (t.1,s.2) t i j).toNat

def inverseRepairProfile (small : I → J → Bool) (B : I → J → ℕ)
    (v : SmallProfile small) (s t : I×J) : SmallProfile small := fun a =>
  if a.2 then B a.1.val.1 a.1.val.2-
    (transferInt (inverseRepairRow small v s t) t s a.1.val.1 a.1.val.2).toNat
  else inverseRepairRow small v s t a.1.val.1 a.1.val.2

lemma inverseRepairRow_repaired (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (s t : I×J)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t)
    (a : Cells small) :
    inverseRepairRow small (repairedProfile small B z s t) s t a.val.1 a.val.2=
      z (a,false) := by
  have heta : (⟨(a.val.1,a.val.2),a.property⟩ : Cells small)=a := Subtype.ext (Prod.eta a.val)
  have he := repairMatrix_cast hd a.val.1 a.val.2
  unfold inverseRepairRow transferInt
  simp only [transferInt,smallView,a.property,dite_eq_left,repairedProfile,
    Bool.false_eq_true,ite_false,heta] at *
  omega

/-- The inverse is evaluated once per ordered defect label; no search
through bounded profiles is needed to recover a predecessor. -/
theorem inverseRepairProfile_repaired (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (s t : I×J)
    (hz : ∀ a,z a ≤ B a.1.val.1 a.1.val.2)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t) :
    inverseRepairProfile small B (repairedProfile small B z s t) s t=z := by
  funext a
  rcases a with ⟨a,b⟩
  cases b
  · exact inverseRepairRow_repaired small B z s t hd a
  · have heta : (⟨(a.val.1,a.val.2),a.property⟩ : Cells small)=a := Subtype.ext (Prod.eta a.val)
    have hr := inverseRepairRow_repaired small B z s t hd a
    have hq := hd.2 a.val.1 a.val.2
    have hb := hz (a,true)
    simp only [inverseRepairProfile,ite_true,transferInt,hr]
    simp only [smallQ,smallView,a.property,dite_eq_left,transferInt,heta] at hq
    dsimp only at hb
    omega

end
end ContingencyTables.SmallGraphProfiles

end OAI
