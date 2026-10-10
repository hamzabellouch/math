import OAI.NumberTheory.DirichletL.Moments.RestrictedSource
import OAI.NumberTheory.DirichletL.Moments.CommonRawCost

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentRestrictedSourceNormalization
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentRestrictedSource
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
open CenteredMomentCommonRawScale CenteredMomentCommonRawCost CenteredMomentRestrictedEnergy
local notation "O" => ActualEisensteinCubic.O

theorem sourceRestrictedEnergy_nonneg (keep : O → Prop) (Q : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (_hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    0≤sourceRestrictedEnergy keep Q c f W K := by
  unfold sourceRestrictedEnergy restrictedEnergy
  apply tsum_nonneg
  intro z
  split_ifs
  · exact mul_nonneg (sq_nonneg _) (hW z)
  · exact le_rfl

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem normalized_restricted_child_energy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (Traw : ℝ) (hTraw : 0<Traw) (hP : ∀ i,0<P i)
    (f : Ideal O → ℂ) (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (sourceRestrictedEnergy keep (residualPool C hC.1 (finiteColumns (Fintype.piFinset S)))
      (fun I => if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0) f W K)/(Traw*∏ i,P i)≤
      ((actualAllocations S C).card:ℝ)*∑ B : actualAllocations S C,
        (‖frozenCoefficient B C R ν Wslot P‖^2/rawReduction B P)*
          ((sourceRestrictedEnergy keep
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K)/remainingRaw B Traw P) := by
  have h := original_restricted_child_energy S hS hp C R s hC hsC ν Wslot P W₁ W₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ f keep W K hK hW
  have htotal : 0<Traw*∏ i,P i := mul_pos hTraw (Finset.prod_pos (fun i _ => hP i))
  apply (div_le_div_of_nonneg_right h htotal.le).trans_eq
  rw [mul_div_assoc,Finset.sum_div]
  apply congrArg (fun x : ℝ => ((actualAllocations S C).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  have hb := (allocation_data S C B (Finset.mem_filter.mp B.property).1).1
  have hr := raw_scale_identity B hb Traw P
  have hpR := rawReduction_pos B hb P hP
  have hpL : 0<remainingRaw B Traw P := by
    apply (mul_pos_iff_of_pos_right hpR).mp
    exact hr.symm ▸ htotal
  have alg (d e n r l : ℝ) (hr : 0<r) (hl : 0<l) (hn : l*r=n) :
      d*e/n=(d/r)*(e/l) := by
    rw [←hn]
    field_simp [hr.ne',hl.ne']
  exact alg _ _ _ _ _ hpR hpL hr

theorem restricted_child_common_saving (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (Traw : ℝ) (hTraw : 0<Traw) (hP : ∀ i,0<P i)
    (M : ι → ℝ) (hν : ∀ i I,‖ν i I‖≤1) (hWnorm : ∀ i x,‖Wslot i x‖≤M i)
    (hM : ∀ i,1≤M i) (a b : ℝ) (ha : 0<a)
    (hslot : ∀ i,Function.support (Wslot i)⊆Set.Icc a b)
    (f : Ideal O → ℂ) (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (sourceRestrictedEnergy keep (residualPool C hC.1 (finiteColumns (Fintype.piFinset S)))
      (fun I => if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0) f W K)/(Traw*∏ i,P i)≤
      ((actualAllocations S C).card:ℝ)*
        (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))*
          ∑ B : actualAllocations S C, ((sourceRestrictedEnergy keep
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K)/remainingRaw B Traw P) := by
  have h := normalized_restricted_child_energy S hS hp C R s hC hsC ν Wslot P W₁ W₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ Traw hTraw hP f keep W K hK hW
  apply h.trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro B hB
  have hb := (allocation_data S C B (Finset.mem_filter.mp B.property).1).1
  have hprod : finiteTupleProduct (B : Tuple ι)=C := (Finset.mem_filter.mp B.property).2
  have hc := frozen_normalized_cost (ι:=ι) (B : Tuple ι) hb C R hC.1 hprod ν Wslot P M hP hν hWnorm hM a b ha hslot
  apply mul_le_mul_of_nonneg_right hc
  have hr := raw_scale_identity B hb Traw P
  have hpR := rawReduction_pos B hb P hP
  have htotal : 0<Traw*∏ i,P i := mul_pos hTraw (Finset.prod_pos (fun i _ => hP i))
  have hpL : 0<remainingRaw B Traw P := (mul_pos_iff_of_pos_right hpR).mp (hr.symm ▸ htotal)
  exact div_nonneg (sourceRestrictedEnergy_nonneg keep _ _ f W K hK hW) hpL.le

end SevenEighths.CenteredMomentRestrictedSourceNormalization

end

end OAI
