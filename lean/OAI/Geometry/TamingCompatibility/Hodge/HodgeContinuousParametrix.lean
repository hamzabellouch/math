import Mathlib
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeHeatWeight
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGammaFubini
import OAI.Geometry.TamingCompatibility.Hodge.HodgePointKernelBounds

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hE in
lemma globalCorrection_continuous_bounds (n : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ T L C : ℝ, 0 < T ∧ T ≤ 1 ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T L (globalLeading J α ht A E) ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T C (globalCorrection J α ht A E T) ∧
      (∀ t ∈ Ioc 0 T, Continuous (fun p : X × X => globalCorrection J α ht A E T t p.1 p.2)) ∧
      (∀ t ∈ Ioc 0 T, Continuous (fun p : X × X => globalError J α ht A E T t p.1 p.2)) ∧
      (∀ t ∈ Ioc 0 T, ∀ x y, globalResidual J α ht A E t x y +
        globalCorrection J α ht A E T t x y +
        VolterraKernel.convolution (geometricVolume A J α) (globalResidual J α ht A E)
          (globalCorrection J α ht A E T) t x y = 0) := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨L,hL⟩ := globalLeading_heatBound J α hs ht A E hE n 1
  obtain ⟨R,hR⟩ := globalResidual_heatBound J α hs ht A E hE n 1
  let T := (8*(R+1))⁻¹
  have hp : 0 < 8*(R+1) := by have := hR.nonneg; positivity
  have hT : 0 < T := inv_pos.mpr hp
  have hT1 : T ≤ 1 := (inv_le_one₀ hp).mpr (by linarith [hR.nonneg])
  have hq : 4*T*R < 1 := by
    dsimp [T]
    rw [show 4*(8*(R+1))⁻¹*R = (4*R)/(8*(R+1)) by ring]
    exact (div_lt_one hp).mpr (by linarith [hR.nonneg])
  have hR' := hR.mono_time _ hT1
  have hC : VolterraKernel.HeatBound (geometricVolume A J α) n T (R/(1-4*T*R))
      (globalCorrection J α ht A E T) :=
    KernelSeries.correction_heatBound (geometricVolume A J α) n hT.le _ hR' hq
  have hRc (t : ℝ) (htp : t ∈ Ioc 0 T) :
      Continuous (fun p : X × X => globalResidual J α ht A E t p.1 p.2) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (globalResidual_continuousAt A J α hs ht E hE htp.1 p.1 p.2).comp
      (continuous_const.prodMk continuous_id).continuousAt
  have hCc (t : ℝ) (htp : t ∈ Ioc 0 T) :
      Continuous (fun p : X × X => globalCorrection J α ht A E T t p.1 p.2) :=
    KernelSeries.correction_continuous (geometricVolume A J α) _ hT.le (hR'.weight_zero _) hRc hq htp
  refine ⟨T,L,R/(1-4*T*R),hT,hT1,hL.mono_time _ hT1,hC,hCc,?_,?_⟩
  · intro t htp
    apply VolterraKernel.convolution_continuous (geometricVolume A J α)
      (globalLeading J α ht A E) (globalCorrection J α ht A E T)
      ((hL.mono_time _ hT1).weight_zero _) (hC.weight_zero _) htp ?_ hCc
    intro u hu
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (globalLeading_continuousAt A J α hs ht E hE hu.1 p.1 p.2).comp
      (continuous_const.prodMk continuous_id).continuousAt
  · intro t htp x y
    exact KernelSeries.correction_equation (geometricVolume A J α) n hT.le _ hR' hq htp x y

variable (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

include hE D hD in
lemma globalCandidate_continuous_eq_spectral (n : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ T L C : ℝ, 0 < T ∧ T ≤ 1 ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T L (globalLeading J α ht A E) ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T C (globalCorrection J α ht A E T) ∧
      (∀ t ∈ Ioc 0 T, Continuous (fun p : X × X => globalError J α ht A E T t p.1 p.2)) ∧
      ∀ v : X → FrameSpace A, Continuous v →
      ∃ f : L2 A J α hs ht true,
        (∀ a : PreL2 A J α hs ht true,
          ⟪f,smoothL2 A J α hs ht true a⟫ =
            ∫ y, framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α) ∧
        (∀ a : PreL2 A J α hs ht true, ∀ t ∈ Ioc 0 T,
          ⟪hodgeSpectralHeat A J α hs ht D hD t f,smoothL2 A J α hs ht true a⟫ =
            kernelWeakAction A J α ht E (globalLeading J α ht A E) v a.val t +
            kernelWeakAction A J α ht E (globalError J α ht A E T) v a.val t) := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨T,L,C,hT,hT1,hL,hC,_hCc,hEc,hcancel⟩ := globalCorrection_continuous_bounds A J α hs ht E hE n
  refine ⟨T,L,C,hT,hT1,hL,hC,hEc,?_⟩
  intro v hv
  obtain ⟨f,U,M,hM,hzero,hbound,hf,hpair,hcont,hweak⟩ :=
    globalCandidate_evolution_of_bounds A J α hs ht E hE hT hT1
      (hL.weight_zero _) (hC.weight_zero _) hcancel v hv
  have he := hodgeBoundedWeakHeat_eq_spectral A J α hs ht D hD f U hT.le hM hbound hcont hzero hweak
  refine ⟨f,hf,?_⟩
  intro a t ht'
  rw [← he t ⟨ht'.1.le,ht'.2⟩]
  exact hpair a t ht'

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.HodgeKernelBounds
open Set Filter MeasureTheory
variable {X B : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

lemma gammaKernel_pairing_iterated (μ : Measure X) [IsFiniteMeasure μ]
    (q k : ℕ) (hqk : q+k=5) {T r A : ℝ} (hr : 0 < r) (hA : 0 ≤ A)
    (K : ℝ → X → X → B)
    (hKm : StronglyMeasurable (fun p : ℝ × X × X => K p.1 p.2.1 p.2.2))
    (hK : ∀ t ∈ Ioc 0 T, ∀ x y, ‖K t x y‖ ≤ A/t^k)
    (Θ : X × X → B →L[ℝ] ℝ) (hΘm : StronglyMeasurable Θ)
    {M : ℝ} (hM : 0 ≤ M) (hΘ : ∀ p, ‖Θ p‖ ≤ M) :
    (∫ x, ∫ y, Θ (x,y) (gammaKernel K T r x y) ∂μ ∂μ) =
      (1/120 : ℝ) * ∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s *
        (∫ x, ∫ y, Θ (x,y) (K (r^2*s) x y) ∂μ ∂μ) := by
  have hg : ∃ C : ℝ, ∀ x y, ‖gammaKernel K T r x y‖ ≤ C := by
    refine ⟨((1/120:ℝ)*A*2^(0-1)*(moment q 1+moment (q+0) 1))/r^(2*k),?_⟩
    intro x y
    have hb := gammaKernel_bound q k 0 hqk hr hA K x y
      ((hKm.comp_measurable (show Measurable (fun s : ℝ => (r^2*s,x,y)) by fun_prop)).aestronglyMeasurable)
      (fun t ht => by simpa only [VolterraBounds.weight,pow_zero,one_mul] using hK t ht x y)
    simpa only [VolterraBounds.weight,pow_zero,one_mul] using hb.2
  obtain ⟨C,hC⟩ := hg
  have higm : StronglyMeasurable (fun p : X × X => Θ p (gammaKernel K T r p.1 p.2)) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      (hΘm.prodMk (gammaKernel_measurable K hKm T r))
  have hig : Integrable (fun p : X × X => Θ p (gammaKernel K T r p.1 p.2)) (μ.prod μ) := by
    apply Integrable.of_bound higm.aestronglyMeasurable (M*C)
    exact Eventually.of_forall fun p => (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hΘ p) (hC p.1 p.2) (norm_nonneg _) hM)
  rw [integral_integral hig,gammaKernel_pairing (μ.prod μ) q k hqk hr K hKm hK Θ hΘm hM hΘ]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hst : r^2*s ∈ Ioc 0 T := ⟨mul_pos (sq_pos_of_pos hr) hs.1,by
    have h := (le_div_iff₀ (sq_pos_of_pos hr)).mp hs.2
    simpa only [mul_comm] using h⟩
  congr 1
  apply integral_prod
  apply Integrable.of_bound
    ((continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      (hΘm.prodMk (hKm.comp_measurable (measurable_const.prodMk measurable_id)))).aestronglyMeasurable
    (M*(A/(r^2*s)^k))
  exact Eventually.of_forall fun p => (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul (hΘ p) (hK _ hst p.1 p.2) (norm_nonneg _) hM)

end TamingCompatibility.GeometricHilbert.HodgeKernelBounds

end
end

end

end OAI
