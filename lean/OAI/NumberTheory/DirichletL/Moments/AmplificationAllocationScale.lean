import OAI.NumberTheory.DirichletL.Moments.AmplificationAllocationCost
import OAI.NumberTheory.DirichletL.Moments.CommonRawScale

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationAllocationScale
open CenteredMomentAmplificationAllocationCost CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentCommonRawScale
open CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

 theorem all_slots_live (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) : liveIndices (B : Tuple ι)=Finset.univ := by
  apply Finset.filter_eq_self.mpr
  intro i hi
  exact allocation_slot_one S P hP k hslot B i

 theorem frozenCoefficient_exact (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) (R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (scale : ι → ℝ) :
    frozenCoefficient B (P^k) R ν Wslot scale=(if IsCoprime (P^k) R then 1 else 0) := by
  unfold frozenCoefficient
  have he : Finset.univ.filter (fun i => B.val (Sum.inl i)≠1)=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i hi
    exact not_not_intro (allocation_slot_one S P hP k hslot B i)
  rw [he,Finset.prod_empty,one_mul]

 theorem frozenCoefficient_norm_le (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) (R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (scale : ι → ℝ) :
    ‖frozenCoefficient B (P^k) R ν Wslot scale‖≤1 := by
  rw [frozenCoefficient_exact S P hP k hslot B R ν Wslot scale]
  split_ifs <;> simp

 theorem rawReduction_exact (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) (scale : ι → ℝ) :
    rawReduction B scale=(Ideal.absNorm P:ℝ)^k := by
  unfold rawReduction plainNorm frozenScale
  simp only [allocation_slot_one S P hP k hslot B,ite_true,Finset.prod_const_one,mul_one]
  rw [← Nat.cast_mul,← map_mul,allocation_plain_product S P hP k hslot B,map_pow,Nat.cast_pow]

 theorem live_slot_card (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) : Fintype.card (liveIndices (B : Tuple ι))=Fintype.card ι := by
  rw [Fintype.card_coe,all_slots_live S P hP k hslot B,Finset.card_univ]

theorem remainingRaw_exact (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) (scale : ι → ℝ) (Traw : ℝ) :
    remainingRaw B Traw scale=(Traw*∏ i,scale i)/(Ideal.absNorm P:ℝ)^k := by
  have hb := (allocation_data S (P^k) B (Finset.mem_filter.mp B.property).1).1
  have he := raw_scale_identity B hb Traw scale
  rw [rawReduction_exact S P hP k hslot B scale] at he
  have hn : (Ideal.absNorm P:ℝ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hP
  exact (eq_div_iff (pow_ne_zero k hn)).mpr he

end SevenEighths.CenteredMomentAmplificationAllocationScale

end

end OAI
