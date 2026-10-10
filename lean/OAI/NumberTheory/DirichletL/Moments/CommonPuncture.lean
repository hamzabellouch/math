import OAI.NumberTheory.DirichletL.Moments.CommonProfile

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonPuncture
open ActualEisensteinCubic CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationBox CenteredMomentFirstSectors
local notation "O" => ActualEisensteinCubic.O

 theorem residualBoxes_filter {ι : Type*} [Fintype ι]
    (S : ι → Finset (Ideal O)) (C : Ideal O) (B : ι → Ideal O) (hB : ∀ i,B i≠0) :
    residualBoxes S C B hB=
      (Fintype.piFinset (fun i => residualPool (B i) (hB i) (S i))).filter
        (fun u => IsCoprime C (∏ i,u i)) := by
  ext u
  simp only [residualBoxes,Fintype.mem_piFinset,Finset.mem_filter,
    IsCoprime.prod_right_iff,Finset.mem_univ,forall_const]
  exact forall_and

theorem residualBoxes_sum {ι : Type*} [Fintype ι]
    (S : ι → Finset (Ideal O)) (C : Ideal O) (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (F : (ι → Ideal O) → ℂ) :
    (∑ u∈residualBoxes S C B hB,F u)=
      ∑ u∈Fintype.piFinset (fun i => residualPool (B i) (hB i) (S i)),
        (if IsCoprime C (∏ i,u i) then 1 else 0)*F u := by
  rw [residualBoxes_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  split_ifs <;> simp

theorem profileCoefficient_puncture {ι : Type*} [Fintype ι]
    (C R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) :
    (if IsCoprime C (finiteTupleProduct v) then 1 else 0)*
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v=
      profileCoefficient (R*C) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v := by
  unfold profileCoefficient
  rw [IsCoprime.mul_right_iff,show IsCoprime C (finiteTupleProduct v) ↔ IsCoprime (finiteTupleProduct v) C from isCoprime_comm]
  by_cases hC : IsCoprime (finiteTupleProduct v) C <;>
    by_cases hR : IsCoprime (finiteTupleProduct v) R <;> simp [hC,hR]

theorem residual_profile_sum {ι : Type*} [Fintype ι]
    (S : (ι ⊕ Fin 2) → Finset (Ideal O)) (C : Ideal O) (B : Tuple ι) (hB : ∀ i,B i≠0)
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O)
    (F : Tuple ι → ℂ) :
    (∑ u∈residualBoxes S C B hB,
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s u*F u)=
      ∑ u∈Fintype.piFinset (fun i => residualPool (B i) (hB i) (S i)),
        profileCoefficient (R*C) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s u*F u := by
  have he (u : Tuple ι) :
      (if IsCoprime C (∏ i,u i) then 1 else 0)*
        profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s u=
        profileCoefficient (R*C) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s u :=
    profileCoefficient_puncture C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s u
  rw [residualBoxes_sum]
  simp_rw [← mul_assoc,he]
  apply Finset.sum_congr
  · ext u
    simp only [Fintype.mem_piFinset]
  · intro u hu
    rfl

end SevenEighths.CenteredMomentCommonPuncture

end

end OAI
