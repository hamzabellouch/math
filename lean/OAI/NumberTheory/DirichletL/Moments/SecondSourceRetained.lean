import OAI.NumberTheory.DirichletL.Moments.SecondRetainedPair

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSourceRetained
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSourceRow CenteredMomentSecondLocalization CenteredMomentSecondSourceEnergy
open CenteredMomentFirstSectors CenteredMomentCompleteCommon CenteredMomentSecondSectorColumns
open CenteredMomentHeckeColumnWindow CenteredMomentSecondSectorRetained CenteredMomentSecondRetainedPair
open CenteredMomentSecondSectorFrequency CenteredMomentSupport CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O

def retainedKernel (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  if hI : Supported I then if hJ : Supported J then secondRetainedPair I J hI hJ W K Tsec Z ξ else 0 else 0

theorem retainedKernel_eq (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) :
    retainedKernel I J W K Tsec Z ξ=secondRetainedPair I J hI hJ W K Tsec Z ξ := by
  simp only [retainedKernel,dite_eq_left hI,dite_eq_left hJ]

theorem retainedEnergy_common_sectors (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) :
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑ p∈commonLabels (supportedColumns S) (supportedColumns S),
        ∑ q∈pairSector p.1 p.2 (supportedColumns S) (supportedColumns S),
          ((β q.1*heightCoeff η t q.1)*star (β q.2*heightCoeff η t q.2))*
            retainedKernel q.1 q.2 W K Tsec Z ξ := by
  let F := fun I J : Ideal O=>((β I*heightCoeff η t I)*star (β J*heightCoeff η t J))*
    retainedKernel I J W K Tsec Z ξ
  have he : secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑ I : supportedColumns S,∑ J : supportedColumns S,F I J := by
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp only [F]
    rw [retainedKernel_eq I J (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2]
  rw [he]
  have hj (I : Ideal O) : (∑ J : supportedColumns S,F I J)=∑ J∈supportedColumns S,F I J :=
    Finset.sum_coe_sort _ _
  simp_rw [hj]
  rw [Finset.sum_coe_sort (supportedColumns S) (fun I=>∑ J∈supportedColumns S,F I J)]
  exact sum_common_sectors _ _ F

theorem retained_sector_independent (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((β q.1*heightCoeff η t q.1)*star (β q.2*heightCoeff η t q.2))*
        retainedKernel q.1 q.2 W K Tsec Z ξ)=
      heightCoeff η t C*star (heightCoeff η t D)*
        ∑ I : sectorPool C hC S,∑ J : sectorPool D hD S,
          if IsCoprime (I:Ideal O) (J:Ideal O) then
            ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
              retainedKernel (C*I) (D*J) W K Tsec Z ξ else 0 := by
  rw [←independent_sector_pools C D hC hD hCD S
    (fun I J=>((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
      retainedKernel (C*I) (D*J) W K Tsec Z ξ)]
  rw [pairSector_double_sum C D hC hD hCD _ _
    (fun I hI=>(Finset.mem_filter.mp hI).2.1) (fun I hI=>(Finset.mem_filter.mp hI).2.1)
    (fun I J=>((β I*heightCoeff η t I)*star (β J*heightCoeff η t J))*
      retainedKernel I J W K Tsec Z ξ)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  split_ifs <;> simp only [heightCoeff_mul,star_mul,mul_zero]
  ring

theorem retainedKernel_physical (C D I J : Ideal O) (hI : Supported (C*I)) (hJ : Supported (D*J))
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) :
    retainedKernel (C*I) (D*J) W K Tsec Z ξ=
      ∑' j : O,idealCorrelation (C*I) (D*J) hI hJ j*
        physicalKernel C D W K (frequencyRadius Tsec Z ξ) j I J := by
  rw [retainedKernel_eq _ _ hI hJ,retainedPair_positive_frequency]
  simp only [physicalKernel,one_mul]

end SevenEighths.CenteredMomentSecondSourceRetained

end

end OAI
