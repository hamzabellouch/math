import Mathlib
import OAI.Analysis.Conductivity.Variational.PhysicalFaceUniqueness

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix

variable {E : Type*}

def sourceFacePasteList (B : Fin 4 → Fin 4 → Coord3 → E) (v : E)
    (ks : List (Fin 4 × Fin 4)) (y : Coord3) : E := by
  classical
  exact ks.foldr (fun k z => if y∈sourceFlatPatch k.1 k.2 then B k.1 k.2 y else z) v

lemma sourceFacePasteList_cons (B : Fin 4 → Fin 4 → Coord3 → E) (v : E)
    (k : Fin 4 × Fin 4) (ks : List (Fin 4 × Fin 4)) (y : Coord3) :
    sourceFacePasteList B v (k::ks) y=
      (by classical exact if y∈sourceFlatPatch k.1 k.2 then B k.1 k.2 y else sourceFacePasteList B v ks y) := rfl

lemma sourceFacePasteList_measurable [MeasurableSpace E]
    {B : Fin 4 → Fin 4 → Coord3 → E} (hB : ∀ i j,Measurable (B i j))
    (v : E) (ks : List (Fin 4 × Fin 4)) : Measurable (sourceFacePasteList B v ks) := by
  induction ks with
  | nil => exact measurable_const
  | cons k ks ih =>
    exact Measurable.ite (isCompact_sourceFlatPatch k.1 k.2).measurableSet (hB k.1 k.2) ih

lemma sourceFacePasteList_local (B : Fin 4 → Fin 4 → Coord3 → E) (v : E)
    (ks : List (Fin 4 × Fin 4)) (y : Coord3)
    (hy : ∃ k∈ks,y∈sourceFlatPatch k.1 k.2) :
    ∃ k∈ks,y∈sourceFlatPatch k.1 k.2 ∧ sourceFacePasteList B v ks y=B k.1 k.2 y := by
  classical
  induction ks with
  | nil => simp at hy
  | cons k ks ih =>
    by_cases hk : y∈sourceFlatPatch k.1 k.2
    · exact ⟨k,List.mem_cons_self,hk,by rw [sourceFacePasteList_cons,ite_eq_left hk]⟩
    · obtain ⟨l,hl,hly⟩ := hy
      have hl' : l∈ks := (List.mem_cons.mp hl).resolve_left (by rintro rfl; exact hk hly)
      obtain ⟨l,hl,hly,he⟩ := ih ⟨l,hl',hly⟩
      exact ⟨l,List.mem_cons_of_mem _ hl,hly,by rw [sourceFacePasteList_cons,ite_eq_right hk,he]⟩

lemma sourceFacePasteList_open (B : Fin 4 → Fin 4 → Coord3 → E) (v : E)
    (ks : List (Fin 4 × Fin 4)) (i j : Fin 4) {x : Coord3}
    (hx : x∈sourceCollarOpenBox) (hk : (i,j)∈ks) :
    sourceFacePasteList B v ks (sourceCollarPiece i j x)=B i j (sourceCollarPiece i j x) := by
  obtain ⟨k,_,hy,he⟩ := sourceFacePasteList_local B v ks _
    ⟨(i,j),hk,⟨x,sourceCollarOpenBox_subset hx,rfl⟩⟩
  obtain ⟨z,hz,hze⟩ := hy
  obtain ⟨hi,hj⟩ := sourceCollarPiece_open_unique i j k.1 k.2 hx hz hze.symm
  simpa only [←hi,←hj] using he

def sourceFacePaste (B : Fin 4 → Fin 4 → Coord3 → E) (v : E) : Coord3 → E :=
  sourceFacePasteList B v (Finset.univ : Finset (Fin 4 × Fin 4)).toList

lemma sourceFacePaste_measurable [MeasurableSpace E]
    {B : Fin 4 → Fin 4 → Coord3 → E} (hB : ∀ i j,Measurable (B i j)) (v : E) :
    Measurable (sourceFacePaste B v) := sourceFacePasteList_measurable hB v _

lemma sourceFacePaste_open (B : Fin 4 → Fin 4 → Coord3 → E) (v : E)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) :
    sourceFacePaste B v (sourceCollarPiece i j x)=B i j (sourceCollarPiece i j x) :=
  sourceFacePasteList_open B v _ i j hx (by simp)

lemma measurable_sourceCollarInverse (i j : Fin 4) : Measurable (sourceCollarInverse i j) := by
  unfold sourceCollarInverse squareFaceParameter sourceCollarTime sourceCrossCoordinates sourceRadial
  fun_prop

def flatEndCoordinates (a b : ℝ) (x : Coord3) : Coord3 := ![a*(x 0-b),x 1,x 2]

lemma contDiff_flatEndCoordinates (a b : ℝ) : ContDiff ℝ (↑(⊤:ℕ∞)) (flatEndCoordinates a b) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [flatEndCoordinates] <;> fun_prop

lemma flatEndCoordinates_angles (a b : ℝ) (x : Coord3) :
    torusAngles (flatEndCoordinates a b x)=torusAngles x := rfl

lemma flatEndCoordinates_axial (a b : ℝ) (x : Coord3) :
    flatEndCoordinates a b x 0=a*(x 0-b) := rfl

end ScalarConductivity

end
end

end OAI
