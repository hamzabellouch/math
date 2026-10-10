import Mathlib
import OAI.GroupTheory.FiniteType.BoundaryValue

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open CategoryTheory AlgebraicTopology Limits
open Set Topology
open scoped unitInterval
open Set Topology
open scoped unitInterval
namespace HornElimination
open Set Topology SimplexBoundary SimplexAddition SimplexDegeneracy DuffyTriangle
universe u
variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}
variable (F : C(Simplex (n+3),X)) (h₂ : ∀ s ∈ DoubleBoundary (n+3), F s = x)
variable (a : Fin (n+2))

abbrev earlyFace (i : Fin (n+2)) := basedFace F h₂ i.castSucc.castSucc
abbrev pivotFace := basedFace F h₂ (Fin.last (n+2)).castSucc

def pivotFamily : Fin (n+4) → BasedSimplex.Space (n+2) X x :=
  Fin.lastCases (pivotFace F h₂) (Fin.lastCases (BasedSimplex.const _ x)
    (fun i => if i = a then RotationClass.permute (earlyFace F h₂ i) (SimplexSign.lastSwap (n+1))
      else BasedSimplex.const _ x))

def pivot : C(Simplex (n+3),X) :=
  BasedHorn.fill (Fin.last (n+2)).castSucc (fun j => pivotFamily F h₂ a j.1)

lemma pivot_early (i : Fin (n+2)) :
    (pivot F h₂ a).comp (face i.castSucc.castSucc) =
      if i = a then (RotationClass.permute (earlyFace F h₂ i) (SimplexSign.lastSwap (n+1))).1
      else ContinuousMap.const _ x := by
  have hi : i.castSucc.castSucc ≠ (Fin.last (n+2)).castSucc := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc,Fin.val_last] at hv
    omega
  rw [pivot,BasedHorn.fill_face _ _ ⟨_,hi⟩]
  simp only [pivotFamily, Fin.lastCases_castSucc]
  split_ifs <;> rfl

lemma pivot_last : (pivot F h₂ a).comp (face (Fin.last (n+3))) = (pivotFace F h₂).1 := by
  rw [pivot,BasedHorn.fill_face _ _ ⟨_, (Fin.castSucc_ne_last _).symm⟩]
  simp [pivotFamily]

lemma pivot_double : ∀ s ∈ DoubleBoundary (n+3), pivot F h₂ a s = x :=
  BasedHorn.fill_doubleBoundary _ _

def side (i : Fin (n+2)) : C(Simplex (n+3),X) :=
  if i = a then degenerate (earlyFace F h₂ i) (Fin.last (n+1)).castSucc
  else degenerate (earlyFace F h₂ i) (Fin.last (n+2))

lemma side_last (i : Fin (n+2)) :
    (side F h₂ a i).comp (face (Fin.last (n+3))) = (earlyFace F h₂ i).1 := by
  unfold side
  split_ifs <;> exact degenerate_face_last _ _

lemma side_penult (i : Fin (n+2)) :
    (side F h₂ a i).comp (face (Fin.last (n+2)).castSucc) =
      if i = a then ContinuousMap.const _ x else (earlyFace F h₂ i).1 := by
  unfold side
  split_ifs
  · exact degenerate_face_const _ _ _ (Fin.castSucc_ne_last _).symm
  · exact degenerate_standard_face _

lemma side_prepenult (i : Fin (n+2)) :
    (side F h₂ a i).comp (face (Fin.last (n+1)).castSucc.castSucc) =
      if i = a then (RotationClass.permute (earlyFace F h₂ i) (SimplexSign.lastSwap (n+1))).1
      else ContinuousMap.const _ x := by
  unfold side
  split_ifs
  · exact degenerate_twisted_face _
  · exact degenerate_face_const _ _ _ (Fin.castSucc_ne_last _)

lemma side_small (i : Fin (n+2)) (j : Fin (n+3)) (hj : j.val < n+1) :
    (side F h₂ a i).comp (face j.castSucc) = ContinuousMap.const _ x := by
  unfold side
  split_ifs <;> apply degenerate_face_const <;> intro h <;>
    have hv := congrArg Fin.val h <;> simp only [Fin.val_castSucc,Fin.val_last] at hv <;> omega

def family : Fin (n+5) → C(Simplex (n+3),X) :=
  Fin.lastCases F (Fin.lastCases (ContinuousMap.const _ x)
    (Fin.lastCases (pivot F h₂ a) (side F h₂ a)))

lemma family_ordered (i j : Fin (n+4)) (hij : i ≤ j)
    (hi : i.castSucc ≠ (Fin.last (n+3)).castSucc)
    (hj : j.succ ≠ (Fin.last (n+3)).castSucc) :
    (family F h₂ a i.castSucc).comp (face j) = (family F h₂ a j.succ).comp (face i) := by
  induction i using Fin.lastCases with
  | last => exact (hi rfl).elim
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      simp only [family,Fin.lastCases_castSucc,Fin.succ_last,Fin.lastCases_last]
      induction i using Fin.lastCases with
      | last => simpa only [Fin.lastCases_last,pivotFace,basedFace] using pivot_last F h₂ a
      | cast i => simpa only [Fin.lastCases_castSucc,earlyFace,basedFace] using side_last F h₂ a i
    | cast j =>
      induction j using Fin.lastCases with
      | last =>
        apply False.elim
        apply hj
        apply Fin.ext
        rfl
      | cast j =>
        induction i using Fin.lastCases with
        | last =>
          have hval := Fin.le_iff_val_le_val.mp hij
          simp only [Fin.val_castSucc,Fin.val_last] at hval
          omega
        | cast i =>
          induction j using Fin.lastCases with
          | last =>
            have he : (Fin.last (n+1)).castSucc.castSucc.succ = (Fin.last (n+2)).castSucc.castSucc := Fin.ext rfl
            rw [he]
            simp only [family,Fin.lastCases_castSucc,Fin.lastCases_last]
            exact (side_prepenult F h₂ a i).trans (pivot_early F h₂ a i).symm
          | cast j =>
            have he : j.castSucc.castSucc.castSucc.succ = j.succ.castSucc.castSucc.castSucc := Fin.ext rfl
            rw [he]
            simp only [family,Fin.lastCases_castSucc]
            rw [side_small F h₂ a i j.castSucc.castSucc (by simpa only [Fin.val_castSucc] using j.isLt)]
            symm
            apply side_small
            have hval := Fin.le_iff_val_le_val.mp hij
            simp only [Fin.val_castSucc] at hval ⊢
            omega

lemma family_compatible :
    ∀ (i j : SimplexHorn.Faces (Fin.last (n+3)).castSucc) (s t : Simplex (n+3)),
      face i.1 s = face j.1 t → family F h₂ a i.1 s = family F h₂ a j.1 t :=
  SimplexHorn.compatible_of_ordered _ _ (family_ordered F h₂ a)

def higher : C(Simplex (n+4),X) :=
  SimplexHorn.fill (Fin.last (n+3)).castSucc (fun j => family F h₂ a j.1) (family_compatible F h₂ a)

lemma higher_face (i : Fin (n+5)) (hi : i ≠ (Fin.last (n+3)).castSucc) :
    (higher F h₂ a).comp (face i) = family F h₂ a i :=
  SimplexHorn.fill_face _ _ _ ⟨i,hi⟩

end HornElimination

namespace SimplexBoundary
open Set Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}

lemma face_ordered (i j : Fin (n+2)) (hij : i ≤ j) :
    (face i.castSucc).comp (face j) = (face j.succ).comp (face i) := by
  apply ContinuousMap.ext
  intro s
  have h := face_face i.castSucc j s
  rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr hij),
    Fin.predAbove_castSucc_of_le _ _ hij] at h
  exact h.symm

lemma face_comp_ordered (H : C(Simplex (n+2),X)) (i j : Fin (n+2)) (hij : i ≤ j) :
    (H.comp (face i.castSucc)).comp (face j) = (H.comp (face j.succ)).comp (face i) := by
  rw [ContinuousMap.comp_assoc,ContinuousMap.comp_assoc,face_ordered i j hij]

lemma doubleBoundary_of_faces (F : C(Simplex (n+2),X))
    (f : Fin (n+3) → BasedSimplex.Space (n+1) X x)
    (hf : ∀ i, F.comp (face i) = (f i).1) : ∀ s ∈ DuffyTriangle.DoubleBoundary (n+2), F s = x := by
  rintro s ⟨i,j,hij,hi,hj⟩
  obtain ⟨k,hk⟩ := Fin.exists_succAbove_eq hij.symm
  rw [← face_drop i s hi]
  have he := DFunLike.congr_fun (hf i) (drop i s hi)
  exact he.trans ((f i).2 _ ⟨k,by change s.1 (i.succAbove k) = 0; rw [hk,hj]⟩)

end SimplexBoundary

namespace HornElimination
open Set Topology SimplexBoundary SimplexAddition SimplexDegeneracy DuffyTriangle
universe u
variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}
variable (F : C(Simplex (n+3),X)) (h₂ : ∀ s ∈ DoubleBoundary (n+3), F s = x)
variable (a : Fin (n+2))

def replacementFace : BasedSimplex.Space (n+2) X x :=
  basedFace (pivot F h₂ a) (pivot_double F h₂ a) (Fin.last (n+2)).castSucc

def replacement : C(Simplex (n+3),X) :=
  (higher F h₂ a).comp (face (Fin.last (n+3)).castSucc)

lemma replacement_early (i : Fin (n+2)) :
    (replacement F h₂ a).comp (face i.castSucc.castSucc) =
      if i = a then ContinuousMap.const _ x else (earlyFace F h₂ i).1 := by
  have hi : i.castSucc.castSucc ≤ (Fin.last (n+2)).castSucc := by
    exact Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last _)
  have h := face_comp_ordered (higher F h₂ a) i.castSucc.castSucc (Fin.last (n+2)).castSucc hi
  have he : (Fin.last (n+2)).castSucc.succ = (Fin.last (n+3)).castSucc := Fin.ext rfl
  rw [he,higher_face _ _ _ _ (by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc,Fin.val_last] at hv
    omega)] at h
  simp only [family,Fin.lastCases_castSucc] at h
  exact h.symm.trans (side_penult F h₂ a i)

lemma replacement_pivot :
    (replacement F h₂ a).comp (face (Fin.last (n+2)).castSucc) = (replacementFace F h₂ a).1 := by
  have h := face_comp_ordered (higher F h₂ a) (Fin.last (n+2)).castSucc (Fin.last (n+2)).castSucc le_rfl
  have he : (Fin.last (n+2)).castSucc.succ = (Fin.last (n+3)).castSucc := Fin.ext rfl
  rw [he,higher_face _ _ _ _ (by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc,Fin.val_last] at hv
    omega)] at h
  simp only [family,Fin.lastCases_castSucc,Fin.lastCases_last] at h
  exact h.symm

lemma replacement_last :
    (replacement F h₂ a).comp (face (Fin.last (n+3))) = (basedFace F h₂ (Fin.last (n+3))).1 := by
  have h := face_comp_ordered (higher F h₂ a) (Fin.last (n+3)) (Fin.last (n+3)) le_rfl
  rw [Fin.succ_last,higher_face _ _ _ _ (Fin.castSucc_ne_last _).symm] at h
  simpa only [family,Fin.lastCases_last,replacement,basedFace] using h

def newFaces : Fin (n+4) → BasedSimplex.Space (n+2) X x :=
  Fin.lastCases (basedFace F h₂ (Fin.last (n+3)))
    (Fin.lastCases (replacementFace F h₂ a) (fun i => if i = a then BasedSimplex.const _ x else earlyFace F h₂ i))

lemma replacement_faces (i : Fin (n+4)) :
    (replacement F h₂ a).comp (face i) = (newFaces F h₂ a i).1 := by
  induction i using Fin.lastCases with
  | last => simpa only [newFaces,Fin.lastCases_last] using replacement_last F h₂ a
  | cast i =>
    induction i using Fin.lastCases with
    | last => simpa only [newFaces,Fin.lastCases_castSucc,Fin.lastCases_last] using replacement_pivot F h₂ a
    | cast i =>
      rw [replacement_early]
      simp only [newFaces,Fin.lastCases_castSucc]
      split_ifs <;> rfl

lemma replacement_double : ∀ s ∈ DoubleBoundary (n+3), replacement F h₂ a s = x :=
  doubleBoundary_of_faces _ _ (replacement_faces F h₂ a)

lemma new_basedFace (i : Fin (n+4)) :
    basedFace (replacement F h₂ a) (replacement_double F h₂ a) i = newFaces F h₂ a i :=
  Subtype.ext (replacement_faces F h₂ a i)

end HornElimination

end

end OAI
