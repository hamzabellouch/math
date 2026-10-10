import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemovalPhaseDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template Template.OneSidedPhase HigherBiasSource
open HigherBiasSource.SourceTemplate InitialCharacterScale TemplateOneSidedSupportSurviving HigherBiasSourceWord
attribute [local instance] Classical.propDecidable

private theorem primeGuard_product {I : Type*} [Fintype I] {Q : ℕ}
    (x : I→PrimeUpTo Q) (P : ℕ+) :
    (∏i,if (x i).val.Coprime P then (1:ℂ) else 0)=
      if ∀i,(x i).val.Coprime P then 1 else 0 := by
  by_cases h : ∀i,(x i).val.Coprime P
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro i hi
    exact ite_eq_left (h i)
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ)

theorem sourceSurvivorPhaseMasks_product (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (x : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L))→
      PrimeUpTo s.locations.Q) :
    (∏i,sourceSurvivorPhaseMasks w j P e i (x i).val)=
      sourceCounterpartProduct w j e x *
        if pivotPrimeGuard (sourceWidth w.configuration (wordSize k L)) P x then 1 else 0 := by
  have hx : Sum.elim (fun i=>x (.inl i)) (fun i=>x (.inr i))=x := by
    funext i
    cases i <;> rfl
  unfold sourceSurvivorPhaseMasks
  rw [Finset.prod_mul_distrib,primeGuard_product]
  have he := counterpartSourceMask_product
    (fun i=>sourceScheduledShells w j
      (copiedConstituentOld (schedule k j) j (sourceWidth w.configuration (wordSize k L)) i))
    e (fun i=>x (.inl i)) (fun i=>x (.inr i))
  rw [hx] at he
  rw [he]
  simp [sourceCounterpartProduct,pivotPrimeGuard]

theorem sourceSurvivorPairPhase_eq_masked_self (hj : j<k) (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j) (hroot : h.val.1=h'.val.1)
    (a b : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)))
    (x : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L))→
      PrimeUpTo s.locations.Q) :
    sourceSurvivorPairPhase w j hj P e h h' x =
      sourceMaskedRetainedPairAt w.configuration (wordSize k L) j hj (Equiv.refl _) e.symm
        (familyCharacter s.family) (familyCenter s.family) (sourceScheduledUnits w j)
        (sourceSurvivorPhaseMasks w j P e) x a b (x a) (x b) P h.val.1 h.val.2 h'.val.2 := by
  have hx : Sum.elim (fun i=>x (.inl i)) (fun i=>x (.inr i))=x := by
    funext i
    cases i <;> rfl
  have he := sourceRetainedPairAt_self w.configuration (wordSize k L) j hj e
    (familyCharacter s.family) (familyCenter s.family) (sourceScheduledUnits w j)
    (fun i=>x (.inl i)) (fun i=>x (.inr i)) a b P h.val.1 h.val.2 h'.val.2
  dsimp only at he
  rw [hx] at he
  have he' : sourceRetainedPairAt w.configuration (wordSize k L) j hj (Equiv.refl _) e.symm
        (familyCharacter s.family) (familyCenter s.family) (sourceScheduledUnits w j)
        x a b (x a) (x b) P h.val.1 h.val.2 h'.val.2 =
      sourceRetainedUnitPhase w j hj P h x *
        conj (sourceRetainedUnitPhase w j hj P h' (sourceCounterpartSample w j e x)) := by
    simpa only [sourceRetainedUnitPhase,sourceCounterpartSample,Sum.elim_inl,Sum.elim_inr,
      Function.comp_def,hroot] using he
  unfold sourceSurvivorPairPhase sourceMaskedRetainedPairAt
  rw [twoPrimeSample_self,sourceSurvivorPhaseMasks_product,he']
  by_cases hp : Pairwise (fun i v=>(x i).val.Coprime (x v).val)
  · by_cases hP : pivotPrimeGuard (sourceWidth w.configuration (wordSize k L)) P x
    · simp only [hp,hP,and_self,ite_true,mul_one,mul_assoc]
    · simp only [hp,hP,and_false,ite_false,ite_true,mul_zero,zero_mul]
  · simp only [hp,false_and,ite_false]

end
end Ostmann.Characters.DiagonalEstimate

end

end OAI
