import OAI.Analysis.StrictMeans.GridLinear

namespace OAI

section
open Polynomial Set Module
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma chainSpace_mono {S T : Set (ℕ × ℕ)} (hST : S ⊆ T) : chainSpace S ≤ chainSpace T := by
  intro p hp
  rw [mem_chainSpace] at hp ⊢
  exact fun i j ht => hp i j (fun hs => ht (hST hs))

lemma chainSpace_shift_x {S T : Set (ℕ × ℕ)} (hST : ∀ i j, (i,j) ∈ S → (i+1,j) ∈ T)
    {p : Chain} (hp : p ∈ chainSpace S) : x*p ∈ chainSpace T := by
  rw [mem_chainSpace] at hp ⊢
  intro i j ht
  cases i with
  | zero => exact coeff_x_zero p j
  | succ i =>
    rw [coeff_x_succ]
    exact hp i j (fun hs => ht (hST i j hs))

lemma chainSpace_shift_y {S T : Set (ℕ × ℕ)} (hST : ∀ i j, (i,j) ∈ S → (i,j+1) ∈ T)
    {p : Chain} (hp : p ∈ chainSpace S) : y*p ∈ chainSpace T := by
  rw [mem_chainSpace] at hp ⊢
  intro i j ht
  cases j with
  | zero => exact coeff_y_zero p i
  | succ j =>
    rw [coeff_y_succ]
    exact hp i j (fun hs => ht (hST i j hs))

lemma chainSpace_shift_xy {S T : Set (ℕ × ℕ)} (hST : ∀ i j, (i,j) ∈ S → (i+1,j+1) ∈ T)
    {p : Chain} (hp : p ∈ chainSpace S) : x*y*p ∈ chainSpace T := by
  rw [mul_assoc]
  apply chainSpace_shift_x (S := {v | ∃ j, (v.1,j) ∈ S ∧ v.2=j+1})
  · rintro i r ⟨j,hj,rfl⟩
    exact hST i j hj
  · exact chainSpace_shift_y (S := S) (T := {v | ∃ j, (v.1,j) ∈ S ∧ v.2=j+1}) (fun i j h => ⟨j,h,rfl⟩) hp

lemma boundary₁_mem (S : Set (ℕ × ℕ)) (e : EdgeSpace S) :
    boundary₁ e.1.1 e.2.1.1 e.2.2.1 ∈ chainSpace S := by
  unfold boundary₁
  simp only [sub_mul,one_mul]
  apply (chainSpace S).add_mem
  · apply (chainSpace S).add_mem
    · exact (chainSpace S).sub_mem (chainSpace_shift_x (fun _ _ h => h.2) e.1.2)
        (chainSpace_mono (fun _ h => h.1) e.1.2)
    · exact (chainSpace S).sub_mem (chainSpace_shift_y (fun _ _ h => h.2) e.2.1.2)
        (chainSpace_mono (fun _ h => h.1) e.2.1.2)
  · exact (chainSpace S).sub_mem (chainSpace_shift_xy (fun _ _ h => h.2) e.2.2.2)
      (chainSpace_mono (fun _ h => h.1) e.2.2.2)

lemma faceH_mem (S : Set (ℕ × ℕ)) (f : FaceSpace S) :
    faceH f.1.1 f.2.1 ∈ chainSpace (horizontalSet S) := by
  exact (chainSpace _).sub_mem (chainSpace_mono (S := lowerSet S) (T := horizontalSet S) (fun _ h => ⟨h.1,h.2.1⟩) f.1.2)
    (chainSpace_shift_y (S := upperSet S) (T := horizontalSet S) (fun _ _ h => ⟨h.2.1,h.2.2⟩) f.2.2)
lemma faceV_mem (S : Set (ℕ × ℕ)) (f : FaceSpace S) :
    faceV f.1.1 f.2.1 ∈ chainSpace (verticalSet S) := by
  exact (chainSpace _).sub_mem (chainSpace_shift_x (S := lowerSet S) (T := verticalSet S) (fun _ _ h => ⟨h.2.1,h.2.2⟩) f.1.2)
    (chainSpace_mono (S := upperSet S) (T := verticalSet S) (fun _ h => ⟨h.1,h.2.1⟩) f.2.2)
lemma faceD_mem (S : Set (ℕ × ℕ)) (f : FaceSpace S) :
    faceD f.1.1 f.2.1 ∈ chainSpace (diagonalSet S) := by
  exact (chainSpace _).sub_mem (chainSpace_mono (S := upperSet S) (T := diagonalSet S) (fun _ h => ⟨h.1,h.2.2⟩) f.2.2)
    (chainSpace_mono (S := lowerSet S) (T := diagonalSet S) (fun _ h => ⟨h.1,h.2.2⟩) f.1.2)

def edgeBoundary (S : Set (ℕ × ℕ)) : EdgeSpace S →ₗ[ℚ] chainSpace S where
  toFun e := ⟨_,boundary₁_mem S e⟩
  map_add' e f := by
    apply Subtype.ext
    exact fullBoundary₁.map_add (e.1.1,e.2.1.1,e.2.2.1) (f.1.1,f.2.1.1,f.2.2.1)
  map_smul' r e := by
    apply Subtype.ext
    exact fullBoundary₁.map_smul r (e.1.1,e.2.1.1,e.2.2.1)

def faceBoundary (S : Set (ℕ × ℕ)) : FaceSpace S →ₗ[ℚ] EdgeSpace S where
  toFun f := (⟨_,faceH_mem S f⟩,⟨_,faceV_mem S f⟩,⟨_,faceD_mem S f⟩)
  map_add' f g := by
    have he := fullBoundary₂.map_add (f.1.1,f.2.1) (g.1.1,g.2.1)
    exact Prod.ext (Subtype.ext (congrArg Prod.fst he))
      (Prod.ext (Subtype.ext (congrArg (fun e => e.2.1) he)) (Subtype.ext (congrArg (fun e => e.2.2) he)))
  map_smul' r f := by
    have he := fullBoundary₂.map_smul r (f.1.1,f.2.1)
    exact Prod.ext (Subtype.ext (congrArg Prod.fst he))
      (Prod.ext (Subtype.ext (congrArg (fun e => e.2.1) he)) (Subtype.ext (congrArg (fun e => e.2.2) he)))

lemma faceBoundary_injective (S : Set (ℕ × ℕ)) : Function.Injective (faceBoundary S) := by
  intro f g he
  have hh : (faceH f.1.1 f.2.1,faceV f.1.1 f.2.1,faceD f.1.1 f.2.1) =
      (faceH g.1.1 g.2.1,faceV g.1.1 g.2.1,faceD g.1.1 g.2.1) :=
    congrArg (fun e : EdgeSpace S => (e.1.1,e.2.1.1,e.2.2.1)) he
  have hf := @face_boundary_injective (f.1.1,f.2.1) (g.1.1,g.2.1) hh
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hf)) (Subtype.ext (congrArg Prod.snd hf))

lemma boundary_exact {u : ℕ × ℕ → ℝ} {c : ℝ}
    (hascent : ∀ i j, c < u (i,j) → 0 < i → 0 < j →
      u (i,j) < u (i+1,j) ∨ u (i,j) < u (i,j+1) ∨
      u (i,j) < u (i-1,j) ∨ u (i,j) < u (i,j-1)) :
    (faceBoundary {w | u w ≤ c}).range = (edgeBoundary {w | u w ≤ c}).ker := by
  let S := {w | u w ≤ c}
  apply le_antisymm
  · rintro _ ⟨f,rfl⟩
    apply Subtype.ext
    exact boundary_face f.1.1 f.2.1
  · intro e he
    have hc : boundary₁ e.1.1 e.2.1.1 e.2.2.1 = 0 := congrArg Subtype.val he
    have hH := (mem_chainSpace (horizontalSet S) e.1.1).mp e.1.2
    have hV := (mem_chainSpace (verticalSet S) e.2.1.1).mp e.2.1.2
    have hD := (mem_chainSpace (diagonalSet S) e.2.2.1).mp e.2.2.2
    obtain ⟨a,b,ha,hb,hd,hs⟩ := cycle_fills_sublevel hc
      (fun i j h => hH i j (by intro hw; exact h.elim (fun hh => (not_lt_of_ge hw.1) hh) (fun hh => (not_lt_of_ge hw.2) hh)))
      (fun i j h => hV i j (by intro hw; exact h.elim (fun hh => (not_lt_of_ge hw.1) hh) (fun hh => (not_lt_of_ge hw.2) hh)))
      (fun i j h => hD i j (by intro hw; exact h.elim (fun hh => (not_lt_of_ge hw.1) hh) (fun hh => (not_lt_of_ge hw.2) hh))) hascent
    have ha' : a ∈ chainSpace (lowerSet S) := (mem_chainSpace _ _).mpr
      (fun i j h => by by_contra hn; exact h (hs.lower i j hn))
    have hb' : b ∈ chainSpace (upperSet S) := (mem_chainSpace _ _).mpr
      (fun i j h => by by_contra hn; exact h (hs.upper i j hn))
    exact ⟨(⟨a,ha'⟩,⟨b,hb'⟩),Prod.ext (Subtype.ext ha) (Prod.ext (Subtype.ext hb) (Subtype.ext hd))⟩

end
end StrictInverseFirstPower.Grid

end

end OAI
