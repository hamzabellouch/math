import OAI.NumberTheory.DirichletL.Moments.DivisorRows

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorRaw
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorSlots
open CenteredMomentDivisorRectangle CenteredMomentDivisorRows CenteredMomentHeckeExpansion
open CenteredMomentHeckeSlots CenteredMomentHeckeHeight HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def frozenIndices (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : Finset ι :=
  Finset.univ.filter (fun i => (selectedPrimes D Finset.univ a (Sum.inl i)).Nonempty)

def liveIndices (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : Finset ι :=
  Finset.univ.filter (fun i => ¬(selectedPrimes D Finset.univ a (Sum.inl i)).Nonempty)

theorem split_slot_product {M : Type*} [CommMonoid M] (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (f : ι → M) :
    (∏ i∈frozenIndices D a,f i)*(∏ i∈liveIndices D a,f i)=∏ i,f i :=
  Finset.prod_filter_mul_prod_filter_not _ _ _

theorem selected_live_slot (η : Character) (m A z : O) (t : ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (i : ι) (hi : i ∈ liveIndices D a) (S : Finset (Ideal O)) (β : Ideal O → ℂ) :
    rowSlot η m A z S (fun I => if selectedSlot D a i∣I then β I else 0) t =
      rowSlot η m A z S β t := by
  have he := selectedDivisor_empty D Finset.univ a (Sum.inl i)
    (Finset.not_nonempty_iff_eq_empty.mp (Finset.mem_filter.mp hi).2)
  simp only [selectedSlot,he,one_dvd,ite_true]

theorem selected_frozen_slot_bound (η : Character) (m A z : O) (t : ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (i : ι) (hi : i ∈ frozenIndices D a) (S : Finset (Ideal O))
    (hS : ∀ I∈S,Prime I) (β : Ideal O → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hβ : ∀ I∈S,‖β I‖ ≤ M) :
    ‖rowSlot η m A z S (fun I => if selectedSlot D a i∣I then β I else 0) t‖ ≤ M := by
  obtain ⟨P,hP⟩ := (Finset.mem_filter.mp hi).2
  exact selected_slot_bound η m A z t (selectedSlot D a i) P
    (IdealMobiusDivisorSum.support_prime P.property) (Finset.dvd_prod_of_mem _ hP)
    S hS β M hM hβ

theorem selected_slot_product_bound (η : Character) (m A z : O) (t : ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (β : ι → Ideal O → ℂ) (M : ι → ℝ) (hM : ∀ i,0 ≤ M i)
    (hβ : ∀ i,∀ I∈S i,‖β i I‖ ≤ M i) :
    (∏ i,‖rowSlot η m A z (S i) (fun I => if selectedSlot D a i∣I then β i I else 0) t‖) ≤
      (∏ i∈frozenIndices D a,M i)*∏ i∈liveIndices D a,‖rowSlot η m A z (S i) (β i) t‖ := by
  rw [← split_slot_product D a]
  apply mul_le_mul
  · apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro i hi
    exact selected_frozen_slot_bound η m A z t D a i hi (S i) (hS i) (β i) (M i) (hM i) (hβ i)
  · apply le_of_eq
    apply Finset.prod_congr rfl
    intro i hi
    rw [selected_live_slot η m A z t D a i hi]
  · exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  · exact Finset.prod_nonneg (fun i _ => hM i)

def selectedNorm (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : ℝ :=
  (Ideal.absNorm (selectedPlain D a 0):ℝ)*(Ideal.absNorm (selectedPlain D a 1):ℝ)

theorem selectedNorm_pos (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) :
    0 < selectedNorm D a := by
  apply mul_pos <;> exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (selectedDivisor_ne_zero D Finset.univ a _))

def rawRemaining (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (T : ℝ) (P : ι → ℝ) : ℝ := (T/selectedNorm D a)*∏ i∈liveIndices D a,P i

def formalReductionFactor (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (P : ι → ℝ) : ℝ := selectedNorm D a*∏ i∈frozenIndices D a,P i

theorem raw_scale_identity (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (T : ℝ) (P : ι → ℝ) :
    rawRemaining D a T P*formalReductionFactor D a P=T*∏ i,P i := by
  unfold rawRemaining formalReductionFactor
  rw [← split_slot_product D a P]
  field_simp [(selectedNorm_pos D a).ne']

end SevenEighths.CenteredMomentDivisorRaw

end

end OAI
