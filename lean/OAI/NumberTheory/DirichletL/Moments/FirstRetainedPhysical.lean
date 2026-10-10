import OAI.NumberTheory.DirichletL.Moments.FirstRetainedSector
import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicAssembly
import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourcePool

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstRetainedPhysical
open ActualEisensteinCubic ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentFirstSectors CenteredMomentFirstSectorTransform CenteredMomentSourceRow
open CenteredMomentFirstRetainedSector CenteredMomentFirstCommonFourierTransport
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSupportedCorrelation CenteredMomentHeckeExpansion CenteredMomentCompleteCommon
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentFirstReduced
local notation "O"=>ActualEisensteinCubic.O

 theorem original_sector_columns (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:C≠0)(hD:D≠0)(hCD:primeSupport C=primeSupport D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    (∑q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*
        retainedKernel q.1 q.2 W K X Z ξ)=
    rowWeight η m A 1 t C*star (rowWeight η m A 1 t D)*
      ∑a:columns C C hC S,∑b:columns C D hD S,
        if IsCoprime (a:Ideal O) (b:Ideal O) then
          (coefficient η m A t c C a*star (coefficient η m A t c D b))*
            retainedKernel (C*a) (D*b) W K X Z ξ else 0:=by
  rw [←original_pool_restriction C D hC hD S
    (fun a b=>(coefficient η m A t c C a*star (coefficient η m A t c D b))*
      retainedKernel (C*a) (D*b) W K X Z ξ)]
  rw [pairSector_double_sum C D hC hD hCD _ _
    (fun I hI=>(Finset.mem_filter.mp hI).2.1) (fun I hI=>(Finset.mem_filter.mp hI).2.1)
    (fun I J=>((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      retainedKernel I J W K X Z ξ)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp only [coefficient,map_mul,star_mul,mul_zero]
  ring

def fixedRetainedSector (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
          fixedRetainedTerm C D hC (element C C hC.1 S a) (element C D hD.1 S b)
            (element_supported C C hC.1 S a) (element_supported C D hD.1 S b) E W K X Z ξ
      else 0

theorem original_sector_fixed (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    (∑q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*
        retainedKernel q.1 q.2 W K X Z ξ)=
    rowWeight η m A 1 t C*star (rowWeight η m A 1 t D)*
      fixedRetainedSector η m A t S c C D hC hD W K X Z ξ:=by
  rw [original_sector_columns η m A t S c C D hC.1 hD.1 hCD W K X Z ξ]
  congr 1
  let F:=fun (a:columns C C hC.1 S) (b:columns C D hD.1 S) (E:Finset (CommonIndex C D))=>
    if IsCoprime (a:Ideal O) (b:Ideal O) then
      (coefficient η m A t c C a*star (coefficient η m A t c D b))*
        fixedRetainedTerm C D hC (element C C hC.1 S a) (element C D hD.1 S b)
          (element_supported C C hC.1 S a) (element_supported C D hD.1 S b) E W K X Z ξ
    else 0
  calc
    _=∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,F a b E:=by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hab:IsCoprime (a:Ideal O) (b:Ideal O)
      · simp only [F,hab,ite_true]
        rw [retainedKernel_fixed C D a b hC hD (column_supported C C hC.1 S a)
          (column_supported C D hD.1 S b) hCD (Finset.mem_filter.mp a.property).2
          (Finset.mem_filter.mp b.property).2 hab W K X Z ξ,Finset.mul_sum]
        rfl
      · simp only [F,hab,ite_false,Finset.sum_const_zero]
    _=∑a:columns C C hC.1 S,∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
      ∑b:columns C D hD.1 S,F a b E:=by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _=fixedRetainedSector η m A t S c C D hC hD W K X Z ξ:=Finset.sum_comm

end SevenEighths.CenteredMomentFirstRetainedPhysical

end

end OAI
