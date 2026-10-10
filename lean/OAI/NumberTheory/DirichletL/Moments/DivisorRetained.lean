import OAI.NumberTheory.DirichletL.Moments.RetainedEnergy
import OAI.NumberTheory.DirichletL.Moments.DivisorRowEnergy

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRows CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentRetainedEnergy CenteredMomentDivisorRowEnergy HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def allocatedPositiveRow (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) : ℂ :=
  retainedPositiveRow η m A z W₁ W₂ (fun i : liveIndices D a => S i)
    (fun i : liveIndices D a => β i) (fun i : liveIndices D a => P i) t
    (X₁/Ideal.absNorm (selectedPlain D a 0)) (X₂/Ideal.absNorm (selectedPlain D a 1))

theorem allocated_to_retained_energy (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (β : ι → Ideal O → ℂ) (M P : ι → ℝ) (hM : ∀ i,0 ≤ M i) (hP : ∀ i,0 < P i)
    (hβ : ∀ i,∀ I∈S i,‖β i I‖ ≤ M i)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) :
    ‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
        allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 ≤
      (2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices D a,M i)^2/formalReductionFactor D a P *
        (‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ X₁ X₂‖^2+
         ‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ Y₁ Y₂‖^2) := by
  have hT : 0 < T := hX ▸ mul_pos hX₁ hX₂
  have hN (j : Fin 2) : (0:ℝ) < Ideal.absNorm (selectedPlain D a j) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  have hx : (X₁/Ideal.absNorm (selectedPlain D a 0))*(X₂/Ideal.absNorm (selectedPlain D a 1))=
      T/selectedNorm D a := by rw [div_mul_div_comm,hX]; rfl
  have hy : (Y₁/Ideal.absNorm (selectedPlain D a 0))*(Y₂/Ideal.absNorm (selectedPlain D a 1))=
      T/selectedNorm D a := by rw [div_mul_div_comm,hY]; rfl
  have hr := allocated_raw_energy η m A z t S hS β M P hM hP hβ D a W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hT
  have hc := centered_to_retained_uniform_energy η m A z W₁ W₂
    (fun i : liveIndices D a => S i) (fun i : liveIndices D a => β i)
    (fun i : liveIndices D a => P i) (fun i => hP i) b₁ b₂ t _ _ _ _ _
    (div_pos hX₁ (hN 0)) (div_pos hX₂ (hN 1)) (div_pos hY₁ (hN 0)) (div_pos hY₂ (hN 1))
    hx hy hW₁ hW₂
  have hF : 0 < formalReductionFactor D a P := mul_pos (selectedNorm_pos D a)
    (Finset.prod_pos (fun i _ => hP i))
  have hh := mul_le_mul_of_nonneg_left hc (div_nonneg (sq_nonneg (∏ i∈frozenIndices D a,M i)) hF.le)
  apply hr.trans
  convert hh using 1 <;> simp only [residualCenteredRow,allocatedPositiveRow] ; ring

theorem masked_raw_to_retained_energy (N : ℕ) (hslots : Fintype.card ι ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (S : ι → Finset (Ideal O)),(∀ i,∀ I∈S i,Prime I) →
      ∀ (β : ι → Ideal O → ℂ) (M P : ι → ℝ),(∀ i,0 ≤ M i) → (∀ i,0 < P i) →
      (∀ i,∀ I∈S i,‖β i I‖ ≤ M i) → ∀ (D : Ideal O),Squarefree D →
      ∀ (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ),
      Function.support W₁ ⊆ Set.Iic b₁ → Function.support W₂ ⊆ Set.Iic b₂ →
      0 < X₁ → 0 < X₂ → 0 < Y₁ → 0 < Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ∀ (rows : Finset O) (ω : O → ℝ),(∀ z∈rows,0 ≤ ω z) →
      (∑ z∈rows,ω z*‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
        maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂‖^2) ≤
      C*(Ideal.absNorm D:ℝ)^ε*
        ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices D a,M i)^2/formalReductionFactor D a P)*
          ∑ z∈rows,ω z*
            (‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ X₁ X₂‖^2+
             ‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ Y₁ Y₂‖^2) := by
  obtain ⟨C,hC,hbase⟩ := actual_allocated_energy (ι := ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η m A t S hS β M P hM hP hβ D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T
    hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hX hY rows ω hω
  have hT : 0 < T := hX ▸ mul_pos hX₁ hX₂
  have htotal : 0 < T*∏ i,P i := mul_pos hT (Finset.prod_pos (fun i _ => hP i))
  have hh := hbase η m A t S β D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂
    hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ rows (fun z => ω z/(T*∏ i,P i))
    (fun z hz => div_nonneg (hω z hz) htotal.le)
  have he (z : O) (x : ℂ) : (ω z/(T*∏ i,P i))*‖x‖^2 =
      ω z*‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*x‖^2 := by
    rw [normalized_norm_sq _ htotal]
    ring
  simp_rw [he] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  apply Finset.sum_le_sum
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  have hb := mul_le_mul_of_nonneg_left
    (allocated_to_retained_energy η m A z t S hS β M P hM hP hβ D a W₁ W₂
      b₁ b₂ X₁ X₂ Y₁ Y₂ T hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hX hY) (hω z hz)
  convert hb using 1 ; ring

end SevenEighths.CenteredMomentDivisorRetained

end

end OAI
