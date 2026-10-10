import OAI.NumberTheory.DirichletL.Moments.FirstMixedRoot
import OAI.NumberTheory.DirichletL.Moments.FirstMixedCommonRadius
import OAI.NumberTheory.DirichletL.Moments.FirstCommonTransport

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedRightTransport
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentActive
open CenteredMomentFirstPhysicalSource CenteredMomentFirstMixedRoot
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstMixedCommonRadius CenteredMomentFirstMixedAllowance
open CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius CenteredMomentDescentLedger
local notation "O" => ActualEisensteinCubic.O

def swapIndex (C D : Ideal O) : CommonIndex C D ≃ CommonIndex D C where
  toFun P := ⟨P.val,by rw [commonSupport_comm];exact P.property⟩
  invFun P := ⟨P.val,by rw [commonSupport_comm];exact P.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma swapIndex_val (C D : Ideal O) (P : CommonIndex C D) :
    (swapIndex C D P).val=P.val := rfl

def swapSubset (C D : Ideal O) (E : Finset (CommonIndex C D)) :
    Finset (CommonIndex D C) := E.map (swapIndex C D).toEmbedding

lemma swapSubset_product (C D : Ideal O) (E : Finset (CommonIndex C D)) :
    (∏P∈swapSubset C D E,P.val)=∏P∈E,P.val := by
  simp only [swapSubset,Finset.prod_map,Equiv.toEmbedding_apply,swapIndex_val]

lemma swapSubset_generator (C D : Ideal O) (E : Finset (CommonIndex C D)) :
    primeSubsetGenerator (fun P : CommonIndex D C=>P.val) (swapSubset C D E)=
      primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E := by
  unfold primeSubsetGenerator
  rw [swapSubset_product]

lemma swapSubset_inactive (C D : Ideal O) (E : Finset (CommonIndex C D)) :
    swapSubset C D E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets D C ↔
      E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D := by
  simp only [CenteredMomentFirstDiscardedEnergy.inactiveSubsets,Finset.mem_powerset]
  constructor
  · intro h P hP
    have hp := h (Finset.mem_map.mpr ⟨P,hP,rfl⟩)
    have hp' := (Finset.mem_filter.mp hp).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change (CenteredExceptionalCount.valuation D P.val + 5 * CenteredExceptionalCount.valuation C P.val) % 6 = 0 at hp'
    change (CenteredExceptionalCount.valuation C P.val + 5 * CenteredExceptionalCount.valuation D P.val) % 6 = 0
    omega
  · intro h P hP
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_map.mp hP
    have hq := (Finset.mem_filter.mp (h hQ)).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change (CenteredExceptionalCount.valuation C Q.val + 5 * CenteredExceptionalCount.valuation D Q.val) % 6 = 0 at hq
    change (CenteredExceptionalCount.valuation D Q.val + 5 * CenteredExceptionalCount.valuation C Q.val) % 6 = 0
    omega

lemma swapped_modulus_factor (C D : Ideal O) (E : Finset (CommonIndex C D)) :
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex D C=>P.val)
      (swapSubset C D E)*activeConductor D C}=
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*activeConductor C D} := by
  rw [swapSubset_generator,←Ideal.span_singleton_mul_span_singleton,
    ←Ideal.span_singleton_mul_span_singleton,active_span_swap]

theorem right_modulus (η : Character) (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayFourExpansion.RayCharacter)
    (F : FixedPair η C D hC E ξ₁ ξ₂) :
    F.right.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex D C=>P.val)
        (swapSubset C D E)*activeConductor D C} := by
  rw [swapped_modulus_factor]
  exact F.right_modulus

lemma nominal_swap (C D E : Ideal O) (K X : ℝ) :
    firstNominalScale D C E K X=firstNominalScale C D E K X := by
  unfold firstNominalScale
  rw [active_span_swap]
  congr 1
  ring

lemma nominalLog_swap (C D E : Ideal O) (K X Z : ℝ) :
    nominalLog D C E K X Z=nominalLog C D E K X Z := by
  unfold nominalLog
  rw [nominal_swap]

theorem right_main_saving (η : Character) (C D E0 : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (ξ₁ ξ₂ : RayFourExpansion.RayCharacter) (F : FixedPair η C D hC E ξ₁ ξ₂)
    (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z) :
    let c := Real.logb Z ((commonPart D C).absNorm:ℝ)
    let d := Real.logb Z ((commonPart C D).absNorm:ℝ)
    let K0 := nominalLog C D E0 K X Z
    2*c/3-4*sigma/3-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) 0 (Real.logb Z (F.right.modulus.absNorm:ℝ)) 0
        (extractedAllowance D C Z)
        (Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j) (sigma/3) := by
  simpa only [nominalLog_swap] using
    actual_main_column_saving η F.right fixedBadMask D C E0 hD hC (swapSubset C D E)
      K X Z j sigma delta reserve hZ (right_modulus η C D hC E ξ₁ ξ₂ F)

theorem right_error_saving (η : Character) (C D E0 : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (ξ₁ ξ₂ : RayFourExpansion.RayCharacter) (F : FixedPair η C D hC E ξ₁ ξ₂)
    (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p : O) (hp : p∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart D C).absNorm:ℝ)
    let d := Real.logb Z ((commonPart C D).absNorm:ℝ)
    let K0 := nominalLog C D E0 K X Z
    2*(c+errorRemoval p Z k)/3-3*sigma/2-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) (errorRemoval p Z k) (Real.logb Z (F.right.modulus.absNorm:ℝ))
        (errorMoving p Z k) (extractedAllowance D C Z)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p k)-j) 0 := by
  simpa only [nominalLog_swap] using
    actual_error_column_saving η F.right fixedBadMask D C E0 hD hC (swapSubset C D E)
      K X Z j sigma delta reserve hZ (right_modulus η C D hC E ξ₁ ξ₂ F)
      M H Sbad hbad p hp k hk

end SevenEighths.CenteredMomentFirstMixedRightTransport

end

end OAI
