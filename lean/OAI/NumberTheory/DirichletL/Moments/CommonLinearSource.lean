import OAI.NumberTheory.DirichletL.Moments.CommonRadialData
import OAI.NumberTheory.DirichletL.Moments.ExceptionalMaskedSource

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonLinearSource
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentEligibleEnergy
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceLiveColumn
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open CenteredMomentOriginalChildEnergy CenteredMomentRestrictedSource CenteredMomentRestrictedDomain
open CenteredMomentAmplificationLiveMask CenteredMomentExceptionalMaskedSource
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def sourceColumn (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)(z:O):ℂ:=
  let Q:=residualPool C hC.1 (finiteColumns (Fintype.piFinset s.pools))
  let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
  rowPolynomial Finset.univ (sourceGenerator Q)
    (fun I:supportedColumns Q=>(if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
      then β (C*I) else 0)*heightCoeff s.η s.t I) z

def liveColumn (s:Input ι)(C R L:Ideal O)(B:actualAllocations s.pools C)(z:O):ℂ:=
  let S:=liveBox s.pools B.val (alloc_ne s C B)
  rowPolynomial Finset.univ (sourceGenerator (finiteColumns S))
    (fun I:supportedColumns (finiteColumns S)=>finiteColumnCoefficient S
      (maskedLiveProfile B.val C R L s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1) I*
        heightCoeff s.η s.t I) z

omit [DecidableEq ι] in
theorem source_column_allocation (s:Input ι)(C:Ideal O)(hC:Supported C)
    (R seed L:Ideal O)(hseed:seed∣C)(z:O):
    sourceColumn s C hC R seed L z=
      ∑B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P*
        liveColumn s C R L B z:=by
  let Q:=residualPool C hC.1 (finiteColumns (Fintype.piFinset s.pools))
  let b:=fun B:actualAllocations s.pools C=>frozenCoefficient B.val C R s.ν s.W s.P
  let d:=fun (B:actualAllocations s.pools C)(I:supportedColumns Q)=>
    finiteColumnCoefficient (liveBox s.pools B.val (alloc_ne s C B))
      (liveProfile B.val C R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1) I*
      ((if L∣(I:Ideal O) then 1 else 0)*heightCoeff s.η s.t I)
  have he (I:supportedColumns Q):
      (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then
        finiteColumnCoefficient (Fintype.piFinset s.pools)
          (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) (C*I)
          else 0)*heightCoeff s.η s.t I=∑B,b B*d B I:=by
    have hc:=original_source_punctured_column s.pools s.pools_ne (fun i J hJ=>s.prime i J hJ)
      C R seed I hC.1 (Finset.mem_filter.mp I.property).2.1 hseed
      s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1
    by_cases hl:L∣(I:Ideal O)
    · simp only [hl,and_true]
      rw [hc,Finset.sum_mul]
      simp only [b,d,hl,ite_true,one_mul,mul_assoc]
    · simp only [hl,and_false,ite_false,zero_mul,b,d,mul_zero,Finset.sum_const_zero]
  change rowPolynomial Finset.univ (sourceGenerator Q) _ z=_
  rw [funext he,rowPolynomial_allocation]
  apply Finset.sum_congr rfl
  intro B hB
  apply congrArg (fun w:ℂ=>b B*w)
  have hh:=live_rowPolynomial s.pools s.pools_ne (fun i J hJ=>s.prime i J hJ)
    B.val (alloc_ne s C B) C R hC (Finset.mem_filter.mp B.property).1
    (Finset.mem_filter.mp B.property).2 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1
    (fun I=>(if L∣I then 1 else 0)*heightCoeff s.η s.t I) z
  change rowPolynomial Finset.univ (sourceGenerator Q) (d B) z=_ at hh
  rw [hh]
  unfold liveColumn
  congr 1
  funext I
  rw [maskedLiveProfile,column_mask]
  dsimp only [liveProfile]
  ring

theorem live_column_rectangle (s:Input ι)(C R L:Ideal O)(B:actualAllocations s.pools C)(z:O):
    liveColumn s C R L B z=
      CenteredMomentDivisorRowEnergy.maskedRectangle
        (commonData s C R B).η (commonData s C R B).m (commonData s C R B).A z
        (commonData s C R B).t (commonData s C R B).slots (commonData s C R B).coefficient L
        (commonData s C R B).W₁ (commonData s C R B).W₂
        (commonData s C R B).X₁ (commonData s C R B).X₂
        (commonData s C R B).Y₁ (commonData s C R B).Y₂:=by
  unfold liveColumn
  rw [CenteredMomentCanonicalRetainedSource.liveBox_original_pools]
  have hc₁:=plainCoverage_residualPool (s.pools (Sum.inr 0)) s.W₁ 1 _
    (alloc_ne s C B (Sum.inr 0)) s.X₁ s.Y₁ s.coverage₁
  have hc₂:=plainCoverage_residualPool (s.pools (Sum.inr 1)) s.W₂ 1 _
    (alloc_ne s C B (Sum.inr 1)) s.X₂ s.Y₂ s.coverage₂
  simp only [one_mul] at hc₁ hc₂
  have he:=CenteredMomentSourceRectangleMask.source_polynomial_eq_maskedRectangle
    s.η fixedBadMask 1 z s.t (dvd_mul_right _ _) (dvd_mul_left _ _)
    (commonData s C R B).slots
    (residualPool (B.val (Sum.inr 0)) (alloc_ne s C B _) (s.pools (Sum.inr 0)))
    (residualPool (B.val (Sum.inr 1)) (alloc_ne s C B _) (s.pools (Sum.inr 1)))
    (R*C) L (commonData s C R B).ν (commonData s C R B).W (commonData s C R B).P
    s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (B.val (Sum.inr 0)) (B.val (Sum.inr 1)) hc₁ hc₂
  rw [height_source_row]
  convert he using 1 <;> simp only [maskedLiveProfile,commonData,one_mul,Input.pools,Sum.elim_inl]
  all_goals rfl

end SevenEighths.CenteredMomentCommonLinearSource

end

end OAI
