import Mathlib
import OAI.Probability.SKBarriers.Parisi.QuantileTransportRemainder
import OAI.Probability.SKBarriers.Scalar.OverlapModulus
import OAI.Probability.SKBarriers.Scalar.SignedCDFTransport

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem quantile_transport_cdf_remainder_strict {k : ℕ} (β : ℝ)
    (A B : Fin (k+1) → ℝ) (hA : A∈admissibleQuantiles k) (hB : B∈admissibleQuantiles k)
    (hgB : ∀ j, 0<cumulativeGapMap k B j) {h : ℝ} (hh : 0<h) :
    |extendedQuantileParisi k β B-extendedQuantileParisi k β A-
      (β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*∫ s in A j..B j, cdfGradientTest β (quantileCDF k A) s|≤
      (β^2/2)*cdfDistance (quantileCDF k B) (quantileCDF k A)*
        scalarOverlapModulus β (cdfDistance (quantileCDF k B) (quantileCDF k A)) h := by
  have hgA := (cumulativeGapMap_nonneg_iff k A).mpr ⟨(hA.2 0).1,hA.1⟩
  have H := quantile_transport_remainder_strict β A B hgA hgB
    (cdfGradientTest_continuous (scalarCDFOverlap_continuousOn_quantile β A hA))
    (M:=scalarOverlapModulus β (cdfDistance (quantileCDF k B) (quantileCDF k A)) h) ?_
  · simpa only [cdfDistance,quantileCDF_L1_eq _ _ hB hA] using H
  intro t ht j
  let Q := (1-t) • A+t • B
  have hQ : Q∈admissibleQuantiles k := admissibleQuantiles_segment hA hB ht
  rw [cdfGradientTest_eq (hQ.2 j),← scalarCDFOverlap_quantile β Q hQ j]
  have he (a b c : ℝ) : (a-b)-(a-c)=c-b := by ring
  rw [he,abs_sub_comm]
  have HS := scalarCDFOverlap_cdf_stability β (quantileCDF_bounds k Q) (quantileCDF_monotone k Q)
    (quantileCDF_bounds k A) (quantileCDF_monotone k A) (hQ.2 j) h hh
  apply HS.trans
  apply scalarOverlapModulus_mono β hh.le
  rw [quantileCDF_segment_distance A B hA hB ht hQ]
  exact mul_le_of_le_one_left (cdfDistance_nonneg _ _) ht.2

theorem quantile_transport_cdf_remainder {k : ℕ} (β : ℝ)
    (A B : Fin (k+1) → ℝ) (hA : A∈admissibleQuantiles k) (hB : B∈admissibleQuantiles k)
    {h : ℝ} (hh : 0<h) :
    |extendedQuantileParisi k β B-extendedQuantileParisi k β A-
      (β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*∫ s in A j..B j, cdfGradientTest β (quantileCDF k A) s|≤
      (β^2/2)*cdfDistance (quantileCDF k B) (quantileCDF k A)*
        scalarOverlapModulus β (cdfDistance (quantileCDF k B) (quantileCDF k A)) h := by
  let R := fun n : ℕ => regularizeQuantile k B (1/((n:ℝ)+1))
  have hε (n : ℕ) : 1/((n:ℝ)+1)∈Ioc (0:ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hgB := (cumulativeGapMap_nonneg_iff k B).mpr ⟨(hB.2 0).1,hB.1⟩
  have hgR (n : ℕ) : ∀ j, 0<cumulativeGapMap k (R n) j := regularizeQuantile_positive B hgB (hε n)
  have hR (n : ℕ) : R n∈admissibleQuantiles k :=
    ⟨((cumulativeGapMap_nonneg_iff k (R n)).mp (fun j => (hgR n j).le)).2,
      regularizeQuantile_mem B hB.2 ⟨(hε n).1.le,(hε n).2⟩⟩
  have HR := regularizeQuantile_tendsto k B
  have HD : Tendsto (fun n => cdfDistance (quantileCDF k (R n)) (quantileCDF k A)) atTop
      (𝓝 (cdfDistance (quantileCDF k B) (quantileCDF k A))) := by
    simp_rw [cdfDistance,quantileCDF_L1_eq _ _ (hR _) hA,quantileCDF_L1_eq _ _ hB hA]
    apply tendsto_finsetSum
    intro j _
    exact tendsto_const_nhds.mul (((tendsto_pi_nhds.mp HR j).sub_const (A j)).abs)
  have HG := cdfGradientTest_continuous (scalarCDFOverlap_continuousOn_quantile β A hA)
  have HI : Tendsto (fun n => ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*
      ∫ s in A j..R n j, cdfGradientTest β (quantileCDF k A) s) atTop
      (𝓝 (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*∫ s in A j..B j, cdfGradientTest β (quantileCDF k A) s)) := by
    apply tendsto_finsetSum
    intro j _
    exact tendsto_const_nhds.mul ((HG.integral_hasStrictDerivAt (A j) (B j)).hasDerivAt.continuousAt.tendsto.comp
      (tendsto_pi_nhds.mp HR j))
  exact le_of_tendsto_of_tendsto
    ((((extendedQuantileParisi_continuous k β).tendsto B |>.comp HR).sub_const _).sub (tendsto_const_nhds.mul HI)).abs
    ((tendsto_const_nhds.mul HD).mul ((scalarOverlapModulus_continuous β h).tendsto _ |>.comp HD))
    (Eventually.of_forall (fun n => quantile_transport_cdf_remainder_strict β A (R n) hA (hR n) (hgR n) hh))

theorem scalarCDFParisi_mass_remainder_quantile {k : ℕ} (β : ℝ)
    (A B : Fin (k+1) → ℝ) (hA : A∈admissibleQuantiles k) (hB : B∈admissibleQuantiles k)
    {h : ℝ} (hh : 0<h) :
    |scalarCDFParisi β (quantileCDF k B)-scalarCDFParisi β (quantileCDF k A)-
      (β^2/2)*∫ s in Icc (0:ℝ) 1, (quantileCDF k B s-quantileCDF k A s)*
        (scalarCDFOverlap β (quantileCDF k A) s-s)|≤
      (β^2/2)*cdfDistance (quantileCDF k B) (quantileCDF k A)*
        scalarOverlapModulus β (cdfDistance (quantileCDF k B) (quantileCDF k A)) h := by
  rw [scalarCDFParisi_quantile β B hB,scalarCDFParisi_quantile β A hA]
  have HG := cdfGradientTest_continuous (scalarCDFOverlap_continuousOn_quantile β A hA)
  have HS := quantileCDF_signed_transport A B hA.2 hB.2 (HG.integrableOn_Icc)
  have he : (∫ s in Icc (0:ℝ) 1, (quantileCDF k B s-quantileCDF k A s)*
      (scalarCDFOverlap β (quantileCDF k A) s-s))=
      ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*∫ s in A j..B j, cdfGradientTest β (quantileCDF k A) s := by
    rw [← neg_inj,← HS,← integral_neg]
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    dsimp only
    rw [cdfGradientTest_eq hs]
    ring
  rw [he]
  exact quantile_transport_cdf_remainder β A B hA hB hh

end SK.Analytic

end
end

end OAI
