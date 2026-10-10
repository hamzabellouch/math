import OAI.NumberTheory.DirichletL.Moments.FirstSectorEnergy
import OAI.NumberTheory.DirichletL.Moments.OriginalChildEnergy
import OAI.NumberTheory.DirichletL.Moments.HeckeColumnWindow

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSourceEnergy
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentLiveDomain
open CenteredMomentOriginalChildEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentFirstSectors CenteredMomentCommonSectors IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

def secondSourceKernel (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑' h : O,(primaryGaussRow I h*star (primaryGaussRow J h))*
    W (‖ConcreteTraceCRT.eisEmbedding h‖^2/K)

theorem heightCoeff_mul (τ : Character) (t : ℝ) (I J : Ideal O) :
    heightCoeff τ t (I*J)=heightCoeff τ t I*heightCoeff τ t J := by
  have hpow : ((Ideal.absNorm I:ℂ)*(Ideal.absNorm J:ℂ))^(Complex.I*t)=
      (Ideal.absNorm I:ℂ)^(Complex.I*t)*(Ideal.absNorm J:ℂ)^(Complex.I*t) := by
    exact_mod_cast Complex.mul_cpow_ofReal_nonneg
      (Nat.cast_nonneg (Ideal.absNorm I):(0:ℝ)≤Ideal.absNorm I)
      (Nat.cast_nonneg (Ideal.absNorm J):(0:ℝ)≤Ideal.absNorm J) (Complex.I*t)
  simp only [heightCoeff,map_mul,Nat.cast_mul,hpow]
  ring

theorem source_energy_common_sectors (τ : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    sourceGaussEnergy S β (heightCoeff τ t) W K=
      ∑ p∈commonLabels (supportedColumns S) (supportedColumns S),
        ∑ q∈pairSector p.1 p.2 (supportedColumns S) (supportedColumns S),
          ((β q.1*heightCoeff τ t q.1)*star (β q.2*heightCoeff τ t q.2))*
            secondSourceKernel q.1 q.2 W K := by
  rw [sourceGaussEnergy,gaussEnergy_expand _ _ _ _ W K hK]
  have hk (I J : supportedColumns S) :
      (∑' h : O,(gaussRow (sourceGenerator S I) (sourceGenerator_supported S I) h*
        star (gaussRow (sourceGenerator S J) (sourceGenerator_supported S J) h))*
          W (‖ConcreteTraceCRT.eisEmbedding h‖^2/K))=secondSourceKernel I J W K := by
    unfold secondSourceKernel
    apply tsum_congr
    intro h
    simp only [primaryGaussRow,dite_eq_left (Finset.mem_filter.mp I.property).2,
      dite_eq_left (Finset.mem_filter.mp J.property).2,sourceGenerator]
  simp_rw [hk]
  let F := fun I J : Ideal O =>
    ((β I*heightCoeff τ t I)*star (β J*heightCoeff τ t J))*secondSourceKernel I J W K
  change (∑ I : supportedColumns S,∑ J : supportedColumns S,F I J)=_
  have he (I : Ideal O) : (∑ J : supportedColumns S,F I J)=∑ J∈supportedColumns S,F I J :=
    Finset.sum_coe_sort (supportedColumns S) (F I)
  simp_rw [he]
  rw [Finset.sum_coe_sort (supportedColumns S) (fun I => ∑ J∈supportedColumns S,F I J)]
  exact sum_common_sectors _ _ _

theorem source_sector_independent_columns (τ : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C D : Ideal O)
    (hC : C≠0) (hD : D≠0) (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((β q.1*heightCoeff τ t q.1)*star (β q.2*heightCoeff τ t q.2))*secondSourceKernel q.1 q.2 W K)=
      heightCoeff τ t C*star (heightCoeff τ t D)*
        ∑ a∈residualPool C hC (supportedColumns S),∑ b∈residualPool D hD (supportedColumns S),
          if IsCoprime C a ∧ IsCoprime C b ∧ IsCoprime a b then
            ((β (C*a)*heightCoeff τ t a)*star (β (D*b)*heightCoeff τ t b))*
              secondSourceKernel (C*a) (D*b) W K else 0 := by
  rw [pairSector_double_sum C D hC hD hCD _ _
    (fun I hI => (Finset.mem_filter.mp hI).2.1)
    (fun I hI => (Finset.mem_filter.mp hI).2.1)
    (fun I J => ((β I*heightCoeff τ t I)*star (β J*heightCoeff τ t J))*secondSourceKernel I J W K),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp only [heightCoeff_mul,star_mul,mul_zero]
  ring

end SevenEighths.CenteredMomentSecondSourceEnergy

end

end OAI
