import OAI.NumberTheory.DirichletL.Moments.DivisorWitness

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorActualBoundary
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle CenteredMomentDivisorRows
open CenteredMomentDivisorRaw CenteredMomentDivisorWitness CenteredMomentSlotRatios HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem selected_log_identity (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) (hv : ∀ i,v i ≠ 0) (P : ι → ℝ) (hP : ∀ i,0 < P i) (Z : ℝ) :
    Real.logb Z (selectedNorm D a*∏ i∈frozenIndices D a,(Ideal.absNorm (v i:Ideal O):ℝ)) =
      Real.logb Z (formalReductionFactor D a P)+
        ∑ i∈frozenIndices D a,Real.logb Z ((Ideal.absNorm (v i:Ideal O):ℝ)/P i) := by
  have hn (i : ι) : (Ideal.absNorm (v i:Ideal O):ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hv i))
  unfold formalReductionFactor
  rw [Real.logb_mul (selectedNorm_pos D a).ne' (Finset.prod_ne_zero_iff.mpr (fun i _ => hn i)),
    Real.logb_mul (selectedNorm_pos D a).ne' (Finset.prod_ne_zero_iff.mpr (fun i _ => (hP i).ne')),
    Real.logb_prod _ _ (fun i _ => hn i),Real.logb_prod _ _ (fun i _ => (hP i).ne')]
  simp_rw [Real.logb_div (hn _) (hP _).ne']
  rw [Finset.sum_sub_distrib]
  ring

theorem nonzero_row_formal_boundary (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (β : ι → Ideal O → ℂ) (W : ι → ℝ → ℂ) (lo hi P : ι → ℝ)
    (hlo : ∀ i,0 < lo i) (hP : ∀ i,0 < P i)
    (hW : ∀ i,Function.support (W i) ⊆ Set.Icc (lo i) (hi i))
    (hβW : ∀ i I,β i I ≠ 0 → W i ((Ideal.absNorm I:ℝ)/P i) ≠ 0)
    (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ Z : ℝ) (hZ : 1 < Z)
    (hne : allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ ≠ 0) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤ Real.logb Z (formalReductionFactor D a P)+
      (∑ i,logWindow (lo i) (hi i))/Real.log Z := by
  obtain ⟨v,I,J,ha,hβ,hrect⟩ := allocated_nonzero_witness η m A z t S β D a
    W₁ W₂ X₁ X₂ Y₁ Y₂ hne
  have hv (i : ι) : (v i:Ideal O) ≠ 0 := (hS i (v i) (v i).property).ne_zero
  have hb := actualExtracted_norm_boundary D hD a (fun i => v i) hv I J ha
  have hND : (0:ℝ) < Ideal.absNorm D := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  have hl := Real.logb_le_logb_of_le hZ hND hb
  rw [selected_log_identity D a (fun i => v i) hv P hP Z] at hl
  have hr : |∑ i∈frozenIndices D a,Real.logb Z ((Ideal.absNorm (v i:Ideal O):ℝ)/P i)| ≤
      (∑ i,logWindow (lo i) (hi i))/Real.log Z := by
    apply frozen_subset_ratio_bound (ι := ι) Finset.univ (frozenIndices D a) (Finset.subset_univ _)
      W lo hi P (fun i => (v i:Ideal O)) Z hZ
    · intro i _
      exact hlo i
    · intro i _
      exact hW i
    · intro i _
      exact hβW i (v i) (hβ i)
  have hh := (le_abs_self (∑ i∈frozenIndices D a,Real.logb Z ((Ideal.absNorm (v i:Ideal O):ℝ)/P i))).trans hr
  linarith

theorem original_nonzero_row_formal_boundary (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (ν : ι → Ideal O → ℂ) (W : ι → ℝ → ℂ) (lo hi P : ι → ℝ)
    (hlo : ∀ i,0 < lo i) (hP : ∀ i,0 < P i)
    (hW : ∀ i,Function.support (W i) ⊆ Set.Icc (lo i) (hi i))
    (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ Z : ℝ) (hZ : 1 < Z)
    (hne : allocatedRectangle η m A z t S
      (fun i I => ν i I*W i ((Ideal.absNorm I:ℝ)/P i)) D a W₁ W₂ X₁ X₂ Y₁ Y₂ ≠ 0) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤ Real.logb Z (formalReductionFactor D a P)+
      (∑ i,logWindow (lo i) (hi i))/Real.log Z :=
  nonzero_row_formal_boundary η m A z t S hS _ W lo hi P hlo hP hW
    (fun _i _I h => (mul_ne_zero_iff.mp h).2) D hD a W₁ W₂ X₁ X₂ Y₁ Y₂ Z hZ hne

end SevenEighths.CenteredMomentDivisorActualBoundary

end

end OAI
