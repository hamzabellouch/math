import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock
import OAI.NumberTheory.DirichletL.Moments.ActiveSource

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondActivePhysicalDictionary
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorColumns
open CenteredMomentSecondSectorFrequency CenteredMomentActiveSource
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentSupport
open CenteredMomentHeckeColumnWindow CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSectorLocalization
open CenteredMomentSecondWholeKernel CenteredMomentLogDyadic
open CenteredMomentSecondSectorRetained CenteredMomentSmooth
local notation "O"=>HeckeFamily.O

 theorem sectorPool_active (C:Ideal O)(hC:C≠0)(S:Finset (Ideal O))(β:Ideal O→ℂ):
    sectorPool C hC (activeSource S β)=(sectorPool C hC S).filter (fun I=>β (C*I)≠0):=by
  ext I
  simp only [sectorPool,Finset.mem_filter,mem_residualPool,supportedColumns_active]
  tauto

 theorem sector_sum_active (C:Ideal O)(hC:C≠0)(S:Finset (Ideal O))(β f:Ideal O→ℂ)
    (hf:∀I,β (C*I)=0→f I=0):
    (∑I∈sectorPool C hC (activeSource S β),f I)=∑I∈sectorPool C hC S,f I:=by
  rw [sectorPool_active,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases h:β (C*I)=0
  · simp only [h,ne_eq,not_true_eq_false,ite_false,hf I h]
  · simp only [h,ne_eq,not_false_eq_true,ite_true]

 theorem sector_pair_sum_active (C D:Ideal O)(hC:C≠0)(hD:D≠0)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(f:Ideal O→Ideal O→ℂ)
    (hleft:∀I J,β (C*I)=0→f I J=0)(hright:∀I J,β (D*J)=0→f I J=0):
    (∑I∈sectorPool C hC (activeSource S β),∑J∈sectorPool D hD (activeSource S β),f I J)=
      ∑I∈sectorPool C hC S,∑J∈sectorPool D hD S,f I J:=by
  simp_rw [sector_sum_active D hD S β _ (fun J h=>hright _ J h)]
  apply sector_sum_active C hC S β
  intro I h
  exact Finset.sum_eq_zero (fun J hJ=>hleft I J h)

 theorem sectorFrequency_active (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(F:O→Ideal O→Ideal O→ℂ)(z:O):
    sectorFrequency η t S β C D hC hD F z=
      sectorFrequency η t (activeSource S β) β C D hC hD F z:=by
  let f:Ideal O→Ideal O→ℂ:=fun I J=>
    if hI:Supported (C*I) then if hJ:Supported (D*J) then
      (if IsCoprime I J then idealCorrelation (C*I) (D*J) hI hJ z else 0)*
        ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*F z I J
      else 0 else 0
  have he (T:Finset (Ideal O)):
      sectorFrequency η t T β C D hC hD F z=
        ∑I∈sectorPool C hC.1 T,∑J∈sectorPool D hD.1 T,f I J:=by
    calc
      _=∑I:sectorPool C hC.1 T,∑J:sectorPool D hD.1 T,f I J:=by
        unfold sectorFrequency
        apply Finset.sum_congr rfl
        intro I hI
        apply Finset.sum_congr rfl
        intro J hJ
        have hc:Supported (C*I):=(supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 T I⟩
        have hd:Supported (D*J):=(supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 T J⟩
        simp only [f,dite_eq_left hc,dite_eq_left hd]
      _=_:=by
        simp_rw [Finset.sum_coe_sort]
        exact Finset.sum_coe_sort (sectorPool C hC.1 T)
          (fun I=>∑J∈sectorPool D hD.1 T,f I J)
  rw [he S,he (activeSource S β)]
  symm
  apply sector_pair_sum_active C D hC.1 hD.1 S β f
  · intro I J h
    simp only [f,h,zero_mul,mul_zero]
    split_ifs <;> rfl
  · intro I J h
    simp only [f,h,zero_mul,star_zero,mul_zero]
    split_ifs <;> rfl

 theorem physicalBlock_active (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t (activeSource S β) β C D hC hD U R rows W K n:=by
  unfold physicalBlock
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  exact sectorFrequency_active η t S β C D hC hD
    (fun j I J=>physicalKernel C D W K R j I J*
      ((dyadicWeight (n 0) (secondEffectiveScale C D
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K)*
        dyadicWeight (n 1) (normValue z)*dyadicWeight (n 2) (I.absNorm:ℝ)*
        dyadicWeight (n 3) (J.absNorm:ℝ):ℝ):ℂ)) _

 theorem normalizedBlock_active (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ):
    normalizedBlock η t S β C D hC hD U R rows W K n=
      normalizedBlock η t (activeSource S β) β C D hC hD U R rows W K n:=by
  unfold normalizedBlock
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  exact sectorFrequency_active η t S β C D hC hD
    (fun _ I J=>wholeKernel W (fun _=>logAnnulus)
      (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
      (Real.log (secondEffectiveScale C D
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K/dyadicScale (n 0)))
      (Real.log (normValue z/dyadicScale (n 1)))
      (Real.log ((I.absNorm:ℝ)/dyadicScale (n 2)))
      (Real.log ((J.absNorm:ℝ)/dyadicScale (n 3)))) _

end SevenEighths.CenteredMomentSecondActivePhysicalDictionary

end

end OAI
