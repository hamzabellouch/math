import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalWindow
import OAI.NumberTheory.DirichletL.Moments.DyadicCount

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondDyadicPartition
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentSecondSectorRetained CenteredMomentSecondPhysicalWindow
open CenteredMomentSecondWholeKernel CenteredMomentFirstWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSmooth CenteredMomentLogDyadic CenteredMomentDyadicCount
local notation "O" => ActualEisensteinCubic.O

abbrev Blocks (a b : Fin 4→ℝ) := ∀ i : Fin 4,↥(indices (a i) (b i))

theorem dyadic_product_partition (a b q : Fin 4→ℝ)
    (ha : ∀i,0<a i) (hq : ∀i,q i∈Set.Icc (a i) (b i)) :
    (∑ n : Blocks a b,∏ i : Fin 4,dyadicWeight (n i) (q i))=1 := by
  change (∑ n : (∀ i : Fin 4,↥(indices (a i) (b i))),∏ i : Fin 4,dyadicWeight (n i) (q i))=1
  rw [←Fintype.prod_sum (fun (i : Fin 4) (n : indices (a i) (b i))=>dyadicWeight n (q i))]
  have he (i : Fin 4) : (∑ n : indices (a i) (b i),dyadicWeight n (q i))=1 := by
    rw [Finset.sum_coe_sort (indices (a i) (b i)) (fun n : ℤ=>dyadicWeight n (q i))]
    exact dyadic_partition_on_interval _ _ _ (ha i) (hq i)
  simp_rw [he]
  simp

theorem physical_kernel_dyadic_partition (C D I J : Ideal O)
    (hC : Supported C) (hD : Supported D) (hI : Supported I) (hJ : Supported J)
    (A h : O) (hA : A≠0) (hh : h≠0) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K)
    (a b : Fin 4→ℝ) (ha : ∀i,0<a i)
    (hband : ∀i, (![secondEffectiveScale C D A K,normValue h,
      (Ideal.absNorm I:ℝ),(Ideal.absNorm J:ℝ)] : Fin 4→ℝ) i∈Set.Icc (a i) (b i)) :
    physicalKernel C D W K R (A*h) I J=
      ∑ n : Blocks a b,
        ((K:ℂ)/((Real.sqrt (Ideal.absNorm C:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm D:ℝ):ℂ)*
          (Real.sqrt (dyadicScale (n 2)):ℂ)*(Real.sqrt (dyadicScale (n 3)):ℂ)))*
          (retainedWeight R (normValue (A*h)):ℂ)*
            wholeKernel W (fun _=>logAnnulus)
              (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
              (Real.log (secondEffectiveScale C D A K/dyadicScale (n 0)))
              (Real.log (normValue h/dyadicScale (n 1)))
              (Real.log ((Ideal.absNorm I:ℝ)/dyadicScale (n 2)))
              (Real.log ((Ideal.absNorm J:ℝ)/dyadicScale (n 3))) := by
  let q : Fin 4→ℝ := ![secondEffectiveScale C D A K,normValue h,
    (Ideal.absNorm I:ℝ),(Ideal.absNorm J:ℝ)]
  have he : (∑ n : Blocks a b,((∏i : Fin 4,dyadicWeight (n i) (q i)):ℝ):ℝ)=1 :=
    dyadic_product_partition a b q ha hband
  calc
    _ = physicalKernel C D W K R (A*h) I J*(1:ℂ) := (mul_one _).symm
    _ = ∑ n : Blocks a b,physicalKernel C D W K R (A*h) I J*
        ((∏i : Fin 4,dyadicWeight (n i) (q i):ℝ):ℂ) := by
      rw [←Finset.mul_sum,←Complex.ofReal_sum,he,Complex.ofReal_one]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Fin.prod_univ_four]
      exact physical_kernel_dyadic C D I J hC hD hI hJ A h hA hh W K R hK (fun i=>n i)

end SevenEighths.CenteredMomentSecondDyadicPartition

end

end OAI
