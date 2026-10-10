import OAI.NumberTheory.DirichletL.Moments.SecondRadicalBlock

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondPhysicalBlock
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondSectorRetained CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport CenteredMomentSectorLocalization
open CenteredMomentSecondRadicalBlock CenteredMomentHeckeColumnWindow
local notation "O" => ActualEisensteinCubic.O

def outerScalar (C D : Ideal O) (K : ℝ) (n : Fin 4→ℤ) : ℝ :=
  K/(Real.sqrt (Ideal.absNorm C:ℝ)*Real.sqrt (Ideal.absNorm D:ℝ)*
    Real.sqrt (dyadicScale (n 2))*Real.sqrt (dyadicScale (n 3)))

def physicalBlock (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (R : ℝ) (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ) : ℂ :=
  let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
  ∑z∈rows,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*z) then
    ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
      (if IsCoprime (I:Ideal O) (J:Ideal O) then
        idealCorrelation (C*I) (D*J)
          ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
          ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
      ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
      (physicalKernel C D W K R (A*z) I J*
        ((dyadicWeight (n 0) (secondEffectiveScale C D A K)*dyadicWeight (n 1) (normValue z)*
          dyadicWeight (n 2) (Ideal.absNorm (I:Ideal O):ℝ)*
          dyadicWeight (n 3) (Ideal.absNorm (J:Ideal O):ℝ):ℝ):ℂ)) else 0

def normalizedBlock (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (R : ℝ) (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ) : ℂ :=
  let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
  ∑z∈rows,retainedScalar C D U R z*
    ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
      (if IsCoprime (I:Ideal O) (J:Ideal O) then
        idealCorrelation (C*I) (D*J)
          ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
          ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
      ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
      wholeKernel W (fun _=>logAnnulus)
        (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
        (Real.log (secondEffectiveScale C D A K/dyadicScale (n 0)))
        (Real.log (normValue z/dyadicScale (n 1)))
        (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/dyadicScale (n 2)))
        (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/dyadicScale (n 3)))

private lemma physicalBlock_scalar (a b c d e f : ℂ) (hb : b ≠ 0) :
    c * d * (a * e * f) = a * b * (b⁻¹ * e * (c * d * f)) := by
  calc
    _ = a * e * (c * d * f) := by ring
    _ = a * (b * b⁻¹) * e * (c * d * f) := by rw [mul_inv_cancel₀ hb, mul_one]
    _ = _ := by ring

theorem physicalBlock_eq (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (R : ℝ) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (n : Fin 4→ℤ) :
    physicalBlock η t S β C D hC hD U R rows W K n=
      (outerScalar C D K n:ℂ)*(normalizer C D U:ℂ)*
        normalizedBlock η t S β C D hC hD U R rows W K n := by
  have hA : commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U≠0 :=
    mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC) (nonunitFrequencyGenerator_ne_zero C D hC U)
  unfold physicalBlock normalizedBlock
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  simp_rw [physical_kernel_dyadic C D _ _ hC hD
    (sectorPool_supported C hC.1 S _) (sectorPool_supported D hD.1 S _)
    _ z hA (hrows z hz) W K R hK n]
  have hn : (normalizer C D U:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (normalizer_pos C D hC U).ne'
  simp only [outerScalar,Complex.ofReal_div,Complex.ofReal_mul,retainedScalar,canonicalPartitionScalar]
  simp only [normalizer] at hn ⊢
  by_cases hp : canonicalPartition C D U (nonunitFrequencyGenerator C D U*z)
  · simp only [hp,ite_true]
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro J hJ
    exact physicalBlock_scalar _ _ _ _ _ _ hn
  · simp only [hp,ite_false,mul_zero,zero_mul,Finset.sum_const_zero]

end SevenEighths.CenteredMomentSecondPhysicalBlock

end

end OAI
