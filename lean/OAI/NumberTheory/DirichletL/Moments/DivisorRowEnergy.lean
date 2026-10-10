import OAI.NumberTheory.DirichletL.Moments.DivisorFullMask
import OAI.NumberTheory.DirichletL.Moments.DivisorEnergy

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorRowEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRows CenteredMomentDivisorFullMask
open CenteredMomentDivisorEnergy CenteredMomentHeckeExpansion CenteredMomentRectangle HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def maskedRectangle (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (D : Ideal O)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  ∑ v : (i : ι) → S i,(∏ i,β i (v i))*
    ∑' I : Ideal O,∑' J : Ideal O,
      (if D∣(∏ i,(v i:Ideal O))*I*J then (1:ℂ) else 0)*
        rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J

theorem actual_allocated_energy (N : ℕ) (hslots : Fintype.card ι ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
      (D : Ideal O),Squarefree D → ∀ (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ),
      Function.support W₁ ⊆ Set.Iic b₁ → Function.support W₂ ⊆ Set.Iic b₂ →
      0 < X₁ → 0 < X₂ → 0 < Y₁ → 0 < Y₂ →
      ∀ (rows : Finset O) (ω : O → ℝ),(∀ z ∈ rows,0 ≤ ω z) →
      (∑ z ∈ rows,ω z*‖maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂‖^2) ≤
        C*(Ideal.absNorm D:ℝ)^ε*
          ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
            ∑ z ∈ rows,ω z*‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 := by
  obtain ⟨C,hC,hcard⟩ := allocation_card_small_power (ι := ι ⊕ Fin 2) (N+2) (by omega) ε hε
  refine ⟨C,hC,?_⟩
  intro η m A t S β D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ rows ω hω
  have hc : (Finset.univ : Finset (ι ⊕ Fin 2)).card ≤ N+2 := by
    simpa only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin] using Nat.add_le_add_right hslots 2
  have hrow (z : O) :
      ‖maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 ≤
        (Fintype.card (Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))):ℝ)*
          ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
            ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 := by
    unfold maskedRectangle
    rw [full_mask_eq_allocated_rectangles η m A z t S β D hD W₁ W₂ b₁ b₂
      _ _ _ _ hW₁ hW₂ hX₁ hX₂ hY₁ hY₂]
    calc
      _ ≤ (∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := by simpa using
        (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun _a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)) => (1:ℝ))
          (fun a => ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖))
  calc
    _ ≤ ∑ z ∈ rows,ω z*((Fintype.card (Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))):ℝ)*
        ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2) :=
      Finset.sum_le_sum (fun z hz => mul_le_mul_of_nonneg_left (hrow z) (hω z hz))
    _ = (Fintype.card (Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))):ℝ)*
        ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          ∑ z ∈ rows,ω z*‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 := by
      simp_rw [mul_left_comm (ω _) _,Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hcard D hD.ne_zero Finset.univ hc)
      (Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun z hz => mul_nonneg (hω z hz) (sq_nonneg _))))

end SevenEighths.CenteredMomentDivisorRowEnergy

end

end OAI
