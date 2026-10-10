import OAI.NumberTheory.DirichletL.Moments.FirstScale
import OAI.NumberTheory.DirichletL.Moments.SectorLocalization

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstDiscarded
open SevenEighths CenteredMomentFirstScale CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CanonicalQuadraticSieve
open CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFirstReduced
open CenteredMomentSupportedCorrelation
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

theorem actual_first_kernel_reference (I J E : Ideal O)
    (hI : I≠0) (hJ : J≠0) (hE : E≠0) (K X HN Tsec : ℝ)
    (hK : 0<K) (hX : 0<X)
    (hi : (Ideal.absNorm I:ℝ)≤Real.exp HN*X)
    (hj : (Ideal.absNorm J:ℝ)≤Real.exp HN*X)
    (hsec : firstNominalScale I J E K X≤Tsec) :
    kernelReference Tsec HN ≤
      K/((Ideal.absNorm E:ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*
        (Ideal.absNorm (residualPart I J):ℝ)*(Ideal.absNorm (residualPart J I):ℝ)) := by
  simpa only [kernelReference,mul_one] using
    first_kernel_sector_lower I J E hI hJ hE K X 1 HN Tsec hK hX zero_le_one hi hj hsec

theorem canonical_discarded_first_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0<C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (I J E : Ideal O) (hI : Supported I) (hJ : Supported J), E≠0 →
      ∀ K X HN Tsec Z Csec ξ : ℝ, 0<K → 0<X → 1<Z → 1≤Csec →
      (Ideal.absNorm I:ℝ)≤Real.exp HN*X → (Ideal.absNorm J:ℝ)≤Real.exp HN*X →
      firstNominalScale I J E K X≤Tsec →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) →
      ‖∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        tripleFourier (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
          (supported_element_ne_zero _ (residualGenerator_supported I J hI))
          (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) h*
        paperRadialFourier W
          ((K/((Ideal.absNorm E:ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*
            (Ideal.absNorm (residualPart I J):ℝ)*(Ideal.absNorm (residualPart J I):ℝ)))*normValue h)‖ ≤
      (‖eisEmbedding (activeConductor I J)‖*(Ideal.absNorm (residualPart I J):ℝ)*
        (Ideal.absNorm (residualPart J I):ℝ))*
        (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := actual_discarded_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro W I J E hI hJ hE K X HN Tsec Z Csec ξ hK hX hZ hCsec hi hj hsec hthreshold
  have hT : 0<Tsec := (firstNominalScale_pos I J E hE K X hK hX).trans_le hsec
  apply ht W Tsec Z Csec HN ξ _ _ hT hZ hCsec hthreshold
    (actual_first_kernel_reference I J E hI.1 hJ.1 hE K X HN Tsec hK hX hi hj hsec)
    (by positivity)
  intro h
  apply (canonical_tripleFourier_norm_le I J hI hJ h).trans
  have ha := CenteredMomentTail.residueGauss_norm_le (residualGenerator I J)
    (supported_element_ne_zero _ (residualGenerator_supported I J hI))
    (residualCharacter I J hI) (Ideal.Quotient.mk _ h)
  have hb := CenteredMomentTail.residueGauss_norm_le (residualGenerator J I)
    (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
    (residualCharacter J I hJ)⁻¹ (Ideal.Quotient.mk _ h)
  have ha' := ha.trans_eq (congrArg (fun L : Ideal O => (Ideal.absNorm L:ℝ))
    (residualGenerator_span I J hI))
  have hb' := hb.trans_eq (congrArg (fun L : Ideal O => (Ideal.absNorm L:ℝ))
    (residualGenerator_span J I hJ))
  exact mul_le_mul (mul_le_mul_of_nonneg_left ha' (norm_nonneg _)) hb' (norm_nonneg _) (by positivity)

end SevenEighths.CenteredMomentFirstDiscarded

end

end OAI
