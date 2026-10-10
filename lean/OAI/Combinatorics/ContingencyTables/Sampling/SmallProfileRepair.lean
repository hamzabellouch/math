import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalGraphVertices
import OAI.Combinatorics.ContingencyTables.Sampling.RepairResiduals

namespace OAI

/-! # Literal small-profile repair and its typewise inverse -/

namespace ContingencyTables.SmallGraphProfiles

open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

noncomputable def repairedProfile (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (s t : I×J) : SmallProfile small := fun a =>
  if a.2 then B a.1.val.1 a.1.val.2-repairMatrix (smallView small z false) s t a.1.val.1 a.1.val.2
  else repairMatrix (smallView small z false) s t a.1.val.1 a.1.val.2

lemma repairMatrix_pointwise (x y : I → J → ℕ) (s t : I×J) (i : I) (j : J)
    (h : x i j=y i j) : repairMatrix x s t i j=repairMatrix y s t i j := by
  simp only [repairMatrix,transferInt,h]

lemma repairedProfile_bounded (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (s t : I×J)
    (hcap : ∀ a : Cells small,repairMatrix (smallView small z false) s t a.val.1 a.val.2 ≤ B a.val.1 a.val.2) :
    ∀ a,repairedProfile small B z s t a ≤ B a.1.val.1 a.1.val.2 := by
  rintro ⟨a,b⟩
  cases b
  · exact hcap a
  · exact Nat.sub_le _ _

lemma repairedProfile_balanced (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (s t : I×J)
    (hcap : ∀ a : Cells small,repairMatrix (smallView small z false) s t a.val.1 a.val.2 ≤ B a.val.1 a.val.2) :
    Balanced small B (repairedProfile small B z s t) := by
  intro i j
  cases hij : small i j
  · simp only [smallView,smallQ,hij,Bool.false_eq_true,↓reduceDIte]
  · simp only [smallView,smallQ,hij,dite_eq_left,repairedProfile,Bool.false_eq_true,↓reduceIte]
    exact (Nat.sub_sub_self (hcap ⟨(i,j),hij⟩)).symm

/-- Fixed ordered defect labels recover both old views from the literal
repaired profile; this does not forget the column-view complement. -/
theorem repairedProfile_injective (small : I → J → Bool) (B : I → J → ℕ)
    (s t : I×J) (z w : SmallProfile small)
    (hz : ∀ a,z a ≤ B a.1.val.1 a.1.val.2) (hw : ∀ a,w a ≤ B a.1.val.1 a.1.val.2)
    (hdz : IsDefect (smallView small z false) (smallQ small B z) s t)
    (hdw : IsDefect (smallView small w false) (smallQ small B w) s t)
    (he : repairedProfile small B z s t=repairedProfile small B w s t) : z=w := by
  have hx (a : Cells small) : z (a,false)=w (a,false) := by
    have heta : (⟨(a.val.1,a.val.2),a.property⟩ : Cells small)=a := Subtype.ext (Prod.eta a.val)
    have hh := congrArg (fun p : SmallProfile small => (p (a,false):ℤ)) he
    change (repairMatrix (smallView small z false) s t a.val.1 a.val.2:ℤ)=
      (repairMatrix (smallView small w false) s t a.val.1 a.val.2:ℤ) at hh
    rw [repairMatrix_cast hdz,repairMatrix_cast hdw] at hh
    simp only [transferInt,smallView,a.property,dite_eq_left] at hh
    simp only [heta] at hh
    omega
  funext a
  rcases a with ⟨a,b⟩
  cases b
  · exact hx a
  · have hdz' := hdz.2 a.val.1 a.val.2
    have hdw' := hdw.2 a.val.1 a.val.2
    have heta : (⟨(a.val.1,a.val.2),a.property⟩ : Cells small)=a := Subtype.ext (Prod.eta a.val)
    simp only [smallQ,smallView,a.property,dite_eq_left,transferInt] at hdz' hdw'
    simp only [heta,hx a] at hdz' hdw'
    have hzb := hz (a,true)
    have hwb := hw (a,true)
    dsimp only at hzb hwb
    omega

end ContingencyTables.SmallGraphProfiles

end OAI
