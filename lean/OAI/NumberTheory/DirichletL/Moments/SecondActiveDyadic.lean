import OAI.NumberTheory.DirichletL.Moments.SecondDyadicPartition
import OAI.NumberTheory.DirichletL.Moments.SecondRetainedRows
import OAI.NumberTheory.DirichletL.Moments.ActiveSource

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondActiveDyadic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondSectorRetained CenteredMomentSecondSectorColumns CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicPartition CenteredMomentSecondWholeKernel CenteredMomentLogDyadic CenteredMomentSmooth
open CenteredMomentActiveSource CenteredMomentSourceRow CenteredMomentSecondRetainedRows
local notation "O" => ActualEisensteinCubic.O

def sourceLower (C D : Ideal O) (A : O) (K : ℝ) : Fin 4→ℝ :=
  ![secondEffectiveScale C D A K,1,1,1]

def sourceUpper (C D : Ideal O) (A : O) (K R H : ℝ) : Fin 4→ℝ :=
  ![secondEffectiveScale C D A K,max 1 (4*R/normValue A),
    max 1 (H/(Ideal.absNorm C:ℝ)),max 1 (H/(Ideal.absNorm D:ℝ))]

def dyadicKernel (C D : Ideal O) (A : O) (W : 𝓢(ℝ,ℂ)) (K R : ℝ)
    (n : Fin 4→ℤ) (h : O) (I J : Ideal O) : ℂ :=
  ((K:ℂ)/((Real.sqrt (Ideal.absNorm C:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm D:ℝ):ℂ)*
    (Real.sqrt (dyadicScale (n 2)):ℂ)*(Real.sqrt (dyadicScale (n 3)):ℂ)))*
    (retainedWeight R (normValue (A*h)):ℂ)*
      wholeKernel W (fun _=>logAnnulus)
        (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
        (Real.log (secondEffectiveScale C D A K/dyadicScale (n 0)))
        (Real.log (normValue h/dyadicScale (n 1)))
        (Real.log ((Ideal.absNorm I:ℝ)/dyadicScale (n 2)))
        (Real.log ((Ideal.absNorm J:ℝ)/dyadicScale (n 3)))

theorem active_sector_norm (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (H : ℝ) (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H)
    (C : Ideal O) (hC : C≠0) (I : sectorPool C hC (activeSource S β)) :
    (Ideal.absNorm (I:Ideal O):ℝ)∈Set.Icc 1 (max 1 (H/(Ideal.absNorm C:ℝ))) := by
  have hh := residualPool_data S β H hH C hC I (Finset.mem_filter.mp I.property).1
  exact ⟨hh.2.2.2.2.1,hh.2.2.2.2.2.trans (le_max_right _ _)⟩

theorem sourceLower_pos (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (A : O) (hA : A≠0) (K : ℝ) (hK : 0<K) : ∀i,0<sourceLower C D A K i := by
  intro i
  fin_cases i
  · exact secondEffectiveScale_pos C D hC hD A hA K hK
  all_goals norm_num [sourceLower]

theorem active_physical_kernel_partition (_η : Character)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (H : ℝ)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (I : sectorPool C hC.1 (activeSource S β)) (J : sectorPool D hD.1 (activeSource S β))
    (A h : O) (hA : A≠0) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    physicalKernel C D W K R (A*h) I J=
      ∑ n : Blocks (sourceLower C D A K) (sourceUpper C D A K R H),
        dyadicKernel C D A W K R (fun i=>n i) h I J := by
  by_cases hw : retainedWeight R (normValue (A*h))=0
  · simp only [physicalKernel,dyadicKernel,hw,Complex.ofReal_zero,mul_zero,zero_mul,Finset.sum_const_zero]
  have he := retainedWeight_enclosure R _ hw
  have hh : h≠0 := by
    intro hz
    subst h
    simp [normValue] at he
  have hrow : normValue h≤4*R/normValue A := by
    apply (le_div_iff₀ (normValue_pos A hA)).mpr
    simpa only [normValue_mul,mul_comm] using he.2
  have hb : ∀i, (![secondEffectiveScale C D A K,normValue h,
      (Ideal.absNorm (I:Ideal O):ℝ),(Ideal.absNorm (J:Ideal O):ℝ)] : Fin 4→ℝ) i∈
        Set.Icc (sourceLower C D A K i) (sourceUpper C D A K R H i) := by
    intro i
    fin_cases i
    · exact ⟨le_rfl,le_rfl⟩
    · exact ⟨normValue_ge_one h hh,hrow.trans (le_max_right _ _)⟩
    · exact active_sector_norm S β H hH C hC.1 I
    · exact active_sector_norm S β H hH D hD.1 J
  exact physical_kernel_dyadic_partition C D I J hC hD
    (sectorPool_supported C hC.1 _ I) (sectorPool_supported D hD.1 _ J)
    A h hA hh W K R hK _ _ (sourceLower_pos C D hC.1 hD.1 A hA K hK) hb

end SevenEighths.CenteredMomentSecondActiveDyadic

end

end OAI
