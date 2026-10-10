import OAI.NumberTheory.DirichletL.Moments.AmplificationLiveEnergy
import OAI.NumberTheory.DirichletL.Moments.AmplificationAllocationScale
import OAI.NumberTheory.DirichletL.Moments.GaussNormalization

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationChildEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentSourceRow
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
open CenteredMomentOriginalChildEnergy CenteredMomentAmplificationLiveMask
open CenteredMomentAmplificationLiveEnergy CenteredMomentAmplificationAllocationScale
open CenteredMomentAmplificationAllocationCost CenteredMomentGaussNormalization
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem actual_amplification_child_energy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (Q R s : Ideal O) (hQ : Prime Q) (hQs : Supported Q) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime Q I)
    (hsc : IsCoprime s (Q^k))
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (f : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (sourceGaussEnergy (residualPool (Q^k) (pow_ne_zero k hQ.ne_zero) (finiteColumns (Fintype.piFinset S)))
      (fun I => if IsCoprime (Q^k) I then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) ((Q^k)*I) else 0) f W K).re≤
      (k+1:ℝ)*∑ B : actualAllocations S (Q^k),
        (sourceGaussEnergy
            (finiteColumns (liveBox S B (allocation_data S (Q^k) B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S (Q^k) B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B (Q^k) R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K).re := by
  have hsPow : ∀ n : ℕ,Supported (Q^n) := by
    intro n
    induction n with
    | zero => simpa only [pow_zero] using CenteredMomentAddedZero.supported_one_ideal
    | succ n ih => rw [pow_succ,supported_mul_iff];exact ⟨ih,hQs⟩
  have hC := hsPow k
  have he := original_masked_child_energy S hS hp (Q^k) R s hC hsc ν Wslot P
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ f W K hK hW
  let E : actualAllocations S (Q^k) → ℝ := fun B =>
    (sourceGaussEnergy
      (finiteColumns (liveBox S B (allocation_data S (Q^k) B (Finset.mem_filter.mp B.property).1).1))
      (finiteColumnCoefficient
        (liveBox S B (allocation_data S (Q^k) B (Finset.mem_filter.mp B.property).1).1)
        (maskedLiveProfile B (Q^k) R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K).re
  have hE (B : actualAllocations S (Q^k)) : 0≤E B := sourceGaussEnergy_nonneg _ _ _ W K hK hW
  have hc : ((actualAllocations S (Q^k)).card:ℝ)≤(k+1:ℝ) := by
    exact_mod_cast actual_amplification_allocations_card S Q hQ k hslot
  have hf (B : actualAllocations S (Q^k)) :
      ‖frozenCoefficient B (Q^k) R ν Wslot P‖^2≤1 := by
    have hh := frozenCoefficient_norm_le S Q hQ.ne_zero k hslot B R ν Wslot P
    nlinarith [norm_nonneg (frozenCoefficient B (Q^k) R ν Wslot P)]
  exact he.trans (mul_le_mul (by exact hc)
    (Finset.sum_le_sum (fun B _ => mul_le_of_le_one_left (hE B) (hf B)))
    (Finset.sum_nonneg (fun B _ => mul_nonneg (sq_nonneg _) (hE B))) (by positivity))

end SevenEighths.CenteredMomentAmplificationChildEnergy

end

end OAI
