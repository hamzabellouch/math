import OAI.NumberTheory.DirichletL.Moments.SecondSourceRetained

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSourceFrequency
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSourceRow CenteredMomentSecondSourceRetained CenteredMomentFirstSectors
open CenteredMomentSecondSectorColumns CenteredMomentHeckeColumnWindow CenteredMomentSecondSectorRetained
open CenteredMomentSecondRetainedPair CenteredMomentSecondSectorFrequency CenteredMomentSupport CenteredMomentSectorLocalization
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst
local notation "O" => ActualEisensteinCubic.O

theorem retained_sector_eq_physical (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((β q.1*heightCoeff η t q.1)*star (β q.2*heightCoeff η t q.2))*
        retainedKernel q.1 q.2 W K Tsec Z ξ)=
      heightCoeff η t C*star (heightCoeff η t D)*
        ∑' j : O,sectorFrequency η t S β C D hC hD
          (physicalKernel C D W K (frequencyRadius Tsec Z ξ)) j := by
  rw [retained_sector_independent η t S β C D hC.1 hD.1 hCD]
  congr 1
  let c := fun I : sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I
  let d := fun J : sectorPool D hD.1 S=>β (D*J)*heightCoeff η t J
  have hci (I : sectorPool C hC.1 S) : Supported (C*(I:Ideal O)) :=
    (supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩
  have hdj (J : sectorPool D hD.1 S) : Supported (D*(J:Ideal O)) :=
    (supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩
  let f := fun (I : sectorPool C hC.1 S) (J : sectorPool D hD.1 S) (j : O)=>
    if IsCoprime (I:Ideal O) (J:Ideal O) then
      (c I*star (d J))*(idealCorrelation (C*I) (D*J) (hci I) (hdj J) j*
        physicalKernel C D W K (frequencyRadius Tsec Z ξ) j I J) else 0
  have hs (I : sectorPool C hC.1 S) (J : sectorPool D hD.1 S) : Summable (f I J) := by
    by_cases hc : IsCoprime (I:Ideal O) (J:Ideal O)
    · simpa only [f,ite_eq_left hc] using (physical_pair_summable C D I J (hci I) (hdj J)
        W K (frequencyRadius Tsec Z ξ) hK).mul_left (c I*star (d J))
    · simp only [f,ite_eq_right hc];exact summable_zero
  have hp (I : sectorPool C hC.1 S) (J : sectorPool D hD.1 S) :
      (if IsCoprime (I:Ideal O) (J:Ideal O) then
        ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
          retainedKernel (C*I) (D*J) W K Tsec Z ξ else 0)=∑' j : O,f I J j := by
    by_cases hc : IsCoprime (I:Ideal O) (J:Ideal O)
    · simp only [f,ite_eq_left hc]
      rw [retainedKernel_physical C D I J (hci I) (hdj J),tsum_mul_left]
    · simp only [f,ite_eq_right hc,tsum_zero]
  have hf (j : O) : sectorFrequency η t S β C D hC hD
      (physicalKernel C D W K (frequencyRadius Tsec Z ξ)) j=
      ∑ I : sectorPool C hC.1 S,∑ J : sectorPool D hD.1 S,f I J j := by
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp only [f,c,d]
    split_ifs <;> ring
  simp_rw [hp]
  rw [tsum_congr hf, Summable.tsum_finsetSum (fun I _=>summable_sum (fun J _=>hs I J))]
  exact Finset.sum_congr rfl (fun I _=>(Summable.tsum_finsetSum (fun J _=>hs I J)).symm)

theorem original_retained_sector_GV (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((β q.1*heightCoeff η t q.1)*star (β q.2*heightCoeff η t q.2))*
        retainedKernel q.1 q.2 W K Tsec Z ξ)=
      heightCoeff η t C*star (heightCoeff η t D)*
        ∑ U : Finset (CommonIndex C D),∑' h : O,
          if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
            sectorFrequency η t S β C D hC hD
              (physicalKernel C D W K (frequencyRadius Tsec Z ξ))
              ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h) else 0 := by
  rw [retained_sector_eq_physical η t S β C D hC hD hCD W K Tsec Z ξ hK,
    actual_retained_sector_GV η t S β C D hC hD hCD W K (frequencyRadius Tsec Z ξ) hK]

end SevenEighths.CenteredMomentSecondSourceFrequency

end

end OAI
