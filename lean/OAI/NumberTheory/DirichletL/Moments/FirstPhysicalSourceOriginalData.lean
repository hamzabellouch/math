import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourcePool
import OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice
import OAI.NumberTheory.DirichletL.Moments.SourceAllocationEnergy
import OAI.NumberTheory.DirichletL.Moments.LiveDomain
import OAI.NumberTheory.DirichletL.Moments.CommonPuncture
import OAI.NumberTheory.DirichletL.Moments.SecondHeightFamily

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentAmplificationLiveMask CenteredMomentLiveDomain CenteredMomentRemainingBox
open CenteredMomentGaussEnergy CenteredMomentSourceAllocationEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentSecondHeightFamily CenteredMomentCommonPuncture CenteredMomentOriginalChildEnergy
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def allocatedData (D:OriginalData ι)(C L:Ideal O)(B:actualAllocations D.S C):
    OriginalData (liveIndices B.val) where
  S:=remainingSets B.val (fun i=>residualPool (B.val i)
    ((allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1 i) (D.S i))
  R:=D.R*C
  s:=L
  nu:=fun i=>D.nu i.val
  slot:=fun i=>D.slot i.val
  lengths:=fun i=>D.lengths i.val
  W₁:=D.W₁
  W₂:=D.W₂
  X₁:=D.X₁
  X₂:=D.X₂
  Y₁:=D.Y₁
  Y₂:=D.Y₂
  B₁:=D.B₁*B.val (Sum.inr 0)
  B₂:=D.B₂*B.val (Sum.inr 1)

lemma allocated_pools (D:OriginalData ι)(C L:Ideal O)(B:actualAllocations D.S C):
    Fintype.piFinset (allocatedData D C L B).S=
      liveBox D.S B.val (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1:=rfl

lemma allocated_profile (D:OriginalData ι)(C L:Ideal O)(B:actualAllocations D.S C):
    (allocatedData D C L B).profile=maskedLiveProfile B.val C D.R L D.nu D.slot D.lengths
      D.W₁ D.W₂ D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂:=rfl

def commonGauss (D:OriginalData ι)(C:Ideal O)(hC:Supported C)(τ:Character)(t:ℝ)(L:Ideal O)(z:O):ℂ:=
  let Q:=residualPool C hC.1 D.columns
  gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I:supportedColumns Q=>(if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
      then D.beta (C*I) else 0)*heightCoeff τ t I) z

theorem common_gauss_allocation (D:OriginalData ι)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (C:Ideal O)(hC:Supported C)(hseed:D.s∣C)(τ:Character)(t:ℝ)(L:Ideal O)(z:O):
    commonGauss D C hC τ t L z=
      ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
        gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported (allocatedData D C L B).columns)
          (fun I=>((allocatedData D C L B).beta I)*heightCoeff τ t I) z:=by
  let Q:=residualPool C hC.1 D.columns
  let b:=fun B:actualAllocations D.S C=>frozenCoefficient B.val C D.R D.nu D.slot D.lengths
  let d:=fun (B:actualAllocations D.S C)(I:supportedColumns Q)=>
    finiteColumnCoefficient (liveBox D.S B.val (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1)
      (liveProfile B.val C D.R D.nu D.slot D.lengths D.W₁ D.W₂ D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂) I*
        ((if L∣(I:Ideal O) then 1 else 0)*heightCoeff τ t I)
  have he (I:supportedColumns Q):
      (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I=
        ∑B,b B*d B I:=by
    have hc:=original_source_punctured_column D.S hS hp C D.R D.s I hC.1
      (Finset.mem_filter.mp I.property).2.1 hseed D.nu D.slot D.lengths D.W₁ D.W₂
      D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂
    change (if IsCoprime C (I:Ideal O) then D.beta (C*I) else 0)=_ at hc
    by_cases hl:L∣(I:Ideal O)
    · simp only [hl,and_true]
      change (if IsCoprime C (I:Ideal O) then _ else 0)*heightCoeff τ t I=_
      rw [hc,Finset.sum_mul]
      simp only [b,d,hl,ite_true,one_mul,mul_assoc]
    · simp only [hl,and_false,ite_false,zero_mul,b,d,mul_zero,Finset.sum_const_zero]
  unfold commonGauss
  change gaussPolynomial Finset.univ (sourceGenerator Q) _ _ z=_
  rw [funext he,gaussPolynomial_allocation]
  apply Finset.sum_congr rfl
  intro B hB
  apply congrArg (fun w:ℂ=>b B*w)
  have hh:=live_gaussPolynomial D.S hS hp B.val
    (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1 C D.R hC
    (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
    D.nu D.slot D.lengths D.W₁ D.W₂ D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂
    (fun I=>(if L∣I then 1 else 0)*heightCoeff τ t I) z
  change gaussPolynomial Finset.univ (sourceGenerator Q) _ (d B) z=_ at hh
  rw [hh]
  congr 1
  funext I
  change _=finiteColumnCoefficient _ (allocatedData D C L B).profile I*heightCoeff τ t I
  rw [allocated_profile,maskedLiveProfile,column_mask]
  dsimp only [liveProfile]
  rw [allocated_pools]
  ring

theorem normalized_common_gauss_allocation (D:OriginalData ι)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (C:Ideal O)(hC:Supported C)(hseed:D.s∣C)(τ:Character)(t T:ℝ)(L:Ideal O)(z:O):
    (Real.sqrt T:ℂ)⁻¹*commonGauss D C hC τ t L z=
      ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
        gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported (allocatedData D C L B).columns)
          ((allocatedData D C L B).coefficient τ fixedBadMask t T) z:=by
  rw [common_gauss_allocation D hS hp C hC hseed τ t L z,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  simp only [OriginalData.coefficient,gaussPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [heightCoeff_eq_fixed_rowWeight τ t I (Finset.mem_filter.mp I.property).2]
  ring

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
