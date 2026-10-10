import OAI.NumberTheory.DirichletL.Moments.FirstSectorTransform
import OAI.NumberTheory.DirichletL.Moments.SecondSourcePoisson
import OAI.NumberTheory.DirichletL.Moments.SecondScaled

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSectorColumns
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondSourceEnergy
open CenteredMomentFirstSectors CenteredMomentFirstSectorTransform CenteredMomentCommonSectors
open CenteredMomentSecondScaled CenteredMomentSupportedCorrelation CenteredMomentChildAssembly
open CenteredMomentFixedRay CenteredMomentMobiusRegroup RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

def sectorPool (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O)) : Finset (Ideal O) :=
  (residualPool C hC (supportedColumns S)).filter (IsCoprime C)

theorem sectorPool_supported (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : Supported (a:Ideal O) :=
  residualPool_supported C hC S ⟨a,(Finset.mem_filter.mp a.property).1⟩

def sectorElement (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : O := primaryGenerator a

theorem sectorElement_span (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : Ideal.span {sectorElement C hC S a}=a :=
  primary_span_supported a (sectorPool_supported C hC S a)

theorem sectorElement_supported (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : Supported (Ideal.span {sectorElement C hC S a}) := by
  rw [sectorElement_span]
  exact sectorPool_supported C hC S a

theorem sectorElement_primary (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : ConcretePrimeRowBridge.goodLambda^2∣sectorElement C hC S a-1 :=
  (primaryGenerator_spec a (supported_primaryGenerator_ne_zero a (sectorPool_supported C hC S a))).2

theorem coprime_of_same_support (C D a : Ideal O) (hC : C≠0) (hD : D≠0) (ha : a≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    IsCoprime C a ↔ IsCoprime D a := by
  change IdealMobiusDivisorSum.primeSupport C=IdealMobiusDivisorSum.primeSupport D at hCD
  rw [←IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC ha,
    ←IdealCoprimeSieveOperator.primeSupport_disjoint_iff hD ha,hCD]

theorem sectorElement_coprime (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (S : Finset (Ideal O)) (a : sectorPool C hC.1 S) :
    IsCoprime (primaryGenerator C*primaryGenerator D) (sectorElement C hC.1 S a) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [←Ideal.span_singleton_mul_span_singleton,primary_span_supported C hC,
    primary_span_supported D hD,sectorElement_span]
  have hc := (Finset.mem_filter.mp a.property).2
  exact hc.mul_left ((coprime_of_same_support C D a hC.1 hD.1
    (sectorPool_supported C hC.1 S a).1 hCD).mp hc)

theorem independent_sector_pools (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (S : Finset (Ideal O)) (F : Ideal O → Ideal O → ℂ) :
    (∑ a∈residualPool C hC (supportedColumns S),∑ b∈residualPool D hD (supportedColumns S),
      if IsCoprime C a ∧ IsCoprime C b ∧ IsCoprime a b then F a b else 0)=
    ∑ a : sectorPool C hC S,∑ b : sectorPool D hD S,
      if IsCoprime (a:Ideal O) (b:Ideal O) then F a b else 0 := by
  have he (a : Ideal O) :
      (∑ b : sectorPool D hD S,if IsCoprime a (b:Ideal O) then F a b else 0)=
      ∑ b∈sectorPool D hD S,if IsCoprime a b then F a b else 0 :=
    Finset.sum_coe_sort (sectorPool D hD S) (fun b : Ideal O => if IsCoprime a b then F a b else 0)
  simp_rw [he]
  rw [Finset.sum_coe_sort (sectorPool C hC S)
    (fun a => ∑ b∈sectorPool D hD S,if IsCoprime a b then F a b else 0)]
  simp only [sectorPool,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hCa : IsCoprime C a
  · simp only [hCa,ite_true,true_and]
    apply Finset.sum_congr rfl
    intro b hb
    have hcb := coprime_of_same_support C D b hC hD
      (residualPool_supported D hD S ⟨b,hb⟩).1 hCD
    by_cases hDb : IsCoprime D b <;> simp [hcb,hDb]
  · simp only [hCa,ite_false,false_and,Finset.sum_const_zero]

end SevenEighths.CenteredMomentSecondSectorColumns

end

end OAI
