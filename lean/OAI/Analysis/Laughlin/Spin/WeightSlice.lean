import OAI.Analysis.Laughlin.Spin.HighestSpace
import OAI.Analysis.Laughlin.Spin.LadderMatrix

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

abbrev SpinIndex (A B : ℕ) := Fin (A+1) × Fin (B+1)

def weightSliceIndex (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (p : Fin (z+1)) : SpinIndex A B := (⟨p.val,by omega⟩,⟨z-p.val,by omega⟩)

theorem weightSliceIndex_injective (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    Function.Injective (weightSliceIndex A B z hA hB) := by
  intro p q h
  exact Fin.ext (congrArg (fun i => i.1.val) h)

noncomputable def extendWeightSlice (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (f : Fin (z+1) → ℝ) (i : SpinIndex A B) : ℝ :=
  ∑ p, if weightSliceIndex A B z hA hB p=i then f p else 0

theorem extendWeightSlice_at (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (f : Fin (z+1) → ℝ) (p : Fin (z+1)) :
    extendWeightSlice A B z hA hB f (weightSliceIndex A B z hA hB p) = f p := by
  simp only [extendWeightSlice,(weightSliceIndex_injective A B z hA hB).eq_iff,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem extendWeightSlice_off (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (f : Fin (z+1) → ℝ) (i : SpinIndex A B) (hi : i.1.val+i.2.val ≠ z) :
    extendWeightSlice A B z hA hB f i = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  have hne : weightSliceIndex A B z hA hB p ≠ i := by
    intro he
    have h₁ := congrArg (fun x => x.1.val) he
    have h₂ := congrArg (fun x => x.2.val) he
    dsimp [weightSliceIndex] at h₁ h₂
    omega
  simp [hne]

theorem sum_extendWeightSlice (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (f : Fin (z+1) → ℝ) (g : SpinIndex A B → ℝ) :
    (∑ i, g i*extendWeightSlice A B z hA hB f i) =
      ∑ p, g (weightSliceIndex A B z hA hB p)*f p := by
  simp only [extendWeightSlice,Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem totalRaise_below_slice (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (f : SpinIndex A B → ℝ) (p : Fin z) :
    (totalRaise A B *ᵥ f) (⟨p.val,by omega⟩,⟨z-p.val-1,by omega⟩) =
      ladder A p.val * f (weightSliceIndex A B z hA hB ⟨p.val+1,by omega⟩) +
      ladder B (z-p.val-1)*f (weightSliceIndex A B z hA hB ⟨p.val,by omega⟩) := by
  change (∑ j, totalRaise A B _ j * f j) = _
  rw [totalRaise_apply,raiseMatrix_row,raiseMatrix_row]
  rw [dite_eq_left (show p.val < A by omega),dite_eq_left (show z-p.val-1 < B by omega)]
  have h₁ : z-(p.val+1)=z-p.val-1 := by omega
  have h₂ : z-p.val-1+1=z-p.val := by omega
  simp only [weightSliceIndex,h₁,h₂]

theorem extendWeightSlice_highest (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (f : Fin (z+1) → ℝ) (hf : ∀ p, raiseSlice A B z f p=0) :
    totalRaise A B *ᵥ extendWeightSlice A B z hA hB f = 0 := by
  funext i
  change (∑ j, totalRaise A B i j * extendWeightSlice A B z hA hB f j) = 0
  by_cases hi : i.1.val+i.2.val+1=z
  · let p : Fin z := ⟨i.1.val,by omega⟩
    have he : i = (⟨p.val,by omega⟩,⟨z-p.val-1,by omega⟩) := by
      apply Prod.ext
      · rfl
      · apply Fin.ext; dsimp [p]; omega
    change (totalRaise A B *ᵥ extendWeightSlice A B z hA hB f) i = 0
    rw [he,totalRaise_below_slice A B z hA hB,extendWeightSlice_at,extendWeightSlice_at]
    exact hf p
  · rw [totalRaise_apply,raiseMatrix_row,raiseMatrix_row]
    have hx (h : i.1.val < A) :
        extendWeightSlice A B z hA hB f (⟨i.1.val+1,by omega⟩,i.2)=0 := by
      apply extendWeightSlice_off
      change i.1.val+1+i.2.val ≠ z
      omega
    have hy (h : i.2.val < B) :
        extendWeightSlice A B z hA hB f (i.1,⟨i.2.val+1,by omega⟩)=0 := by
      apply extendWeightSlice_off
      change i.1.val+(i.2.val+1) ≠ z
      omega
    split_ifs with h₁ h₂ h₂ <;> simp_all only [mul_zero,add_zero]

end Laughlin.Spin

end OAI
