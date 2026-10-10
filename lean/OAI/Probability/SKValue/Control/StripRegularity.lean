import Mathlib
import OAI.Probability.SKValue.Processes.MeshBrownian
import OAI.Probability.SKValue.Evolution.L1Terminal

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

def SourceStripRegularity (W : BrownianSpace) (γ : OrderParameter) : Prop :=
  ∀ T∈Ico (0 : ℝ) 1, ∃ Kv Lv K L D Lu La : ℝ,
    ValueStrip T γ.coeff (phi W γ) Kv Lv ∧
    GradientStrip T γ.coeff (gradient W γ) K L ∧
    0≤D ∧ 0≤Lu ∧ 0≤La ∧
    (∀ t∈Icc (0 : ℝ) T, ∀ x, |curvature W γ t x|≤D) ∧
    (∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |gradient W γ s x-gradient W γ t y|≤Lu*(|s-t|+|x-y|)) ∧
    (∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |curvature W γ s x-curvature W γ t y|≤La*(|s-t|+|x-y|))

lemma SourceStripRegularity.core {W : BrownianSpace} {γ : OrderParameter}
    (h : SourceStripRegularity W γ) :
    ∀ T∈Ico (0 : ℝ) 1, ∃ K L Lu : ℝ, 0≤Lu ∧
      GradientStripCore T γ.coeff (gradient W γ) K L ∧
      ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
        |gradient W γ s x-gradient W γ t y|≤Lu*(|s-t|+|x-y|) := by
  intro T hT
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := h T hT
  exact ⟨K,L,Lu,hLu,hG.toCore,hu⟩

lemma IsDiffusion.curvature_mean_continuous {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (hreg : SourceStripRegularity W γ) :
    ContinuousOn (fun t ↦ ∫ ω, curvature W γ t (X t ω) ∂W.μ) (Ico (0 : ℝ) 1) := by
  intro t ht
  obtain ⟨T,htT,hT1⟩ := exists_between ht.2
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := hreg T ⟨ht.1.trans htT.le,hT1⟩
  have hc := mean_derivative_continuous hLa
    (fun s hs ↦ (hG.smooth s hs).continuous_deriv (by norm_num)) hDb ha
    (fun s hs ↦ (hX.measurable ⟨hs.1,hs.2.trans hT1.le⟩).aestronglyMeasurable)
    (hX.2.mono (fun _ hω ↦ hω.1.mono (Icc_subset_Icc le_rfl hT1.le)))
  apply (hc t ⟨ht.1,htT.le⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htT)] with s hs hsT
  exact ⟨hs.1,hsT.le⟩

lemma IsDiffusion.curvature_memLp {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (hreg : SourceStripRegularity W γ)
    {t : ℝ} (ht : t∈Ico (0 : ℝ) 1) (p : ℝ≥0∞) :
    MemLp (fun ω ↦ curvature W γ t (X t ω)) p W.μ := by
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := hreg t ht
  exact MemLp.of_bound
    (((hG.smooth t ⟨ht.1,le_rfl⟩).continuous_deriv (by norm_num)).measurable.comp
      (hX.measurable ⟨ht.1,ht.2.le⟩)).aestronglyMeasurable D
    (Eventually.of_forall (fun ω ↦ (Real.norm_eq_abs _).trans_le (hDb t ⟨ht.1,le_rfl⟩ _)))

lemma IsDiffusion.curvature_mean_integrable {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (hreg : SourceStripRegularity W γ)
    (ha : ∀ t∈Ico (0 : ℝ) 1, (∫ ω, (curvature W γ t (X t ω))^2 ∂W.μ)=1) :
    IntervalIntegrable (fun t ↦ ∫ ω, curvature W γ t (X t ω) ∂W.μ) volume 0 1 := by
  have hb (t : ℝ) (ht : t∈Ico (0 : ℝ) 1) :
      |∫ ω, curvature W γ t (X t ω) ∂W.μ|≤1 := by
    apply abs_integral_le_integral_abs.trans
    simpa only [ha t ht,Real.sqrt_one] using integral_abs_le_sqrt_second (hX.curvature_memLp hreg ht 2)
  have hi : IntegrableOn (fun t ↦ ∫ ω, curvature W γ t (X t ω) ∂W.μ) (Ico (0 : ℝ) 1) :=
    Integrable.of_bound ((hX.curvature_mean_continuous hreg).aestronglyMeasurable measurableSet_Ico)
      1 ((ae_restrict_mem measurableSet_Ico).mono (fun t ht ↦ (Real.norm_eq_abs _).trans_le (hb t ht)))
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ)≤1)).mpr
    (hi.congr_set_ae Ico_ae_eq_Ioc.symm)

lemma IsDiffusion.terminal_brownian_covariance {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (hreg : SourceStripRegularity W γ)
    (hm : UnitMomentMartingale (μ := W.μ) W.realFiltration (fun t ω ↦ gradient W γ t (X t ω)))
    {U : W.Ω → ℝ} (hUm : StronglyMeasurable[W.realFiltration 1] U)
    (hU : ∀ᵐ ω ∂W.μ, |U ω|≤1 ∧
      Tendsto (fun n ↦ gradient W γ (terminalTime n) (X (terminalTime n) ω)) atTop (𝓝 (U ω)))
    {T : ℝ} (hT : 0<T) (hT1 : T<1) :
    (∫ ω, U ω*W.B T.toNNReal ω ∂W.μ)=
      ∫ t in (0 : ℝ)..T, ∫ ω, curvature W γ t (X t ω) ∂W.μ := by
  have hc := hm.terminal_integral_past hUm hU ⟨hT.le,hT1⟩
    (Filtration.stronglyAdapted_natural W.measurable T.toNNReal)
    (((W.brownian.hasLaw_eval T.toNNReal).hasGaussianLaw.memLp (p := 1) (by norm_num)).integrable le_rfl)
  rw [hc]
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := hreg T ⟨hT.le,hT1⟩
  exact diffusion_gradient_brownian_covariance W.brownian.toIsPreBrownianReal hT hT1.le hG
    hD hLu hLa hDb hu ha
    (fun t ht ↦ (hX.measurable ⟨ht.1,ht.2.trans hT1.le⟩).aestronglyMeasurable)
    (hX.strip_paths hT.le hT1 hLu (fun t ht s hs x y ↦ hu s hs t ht y x))

lemma IsDiffusion.curvature_integral_terminal {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (hreg : SourceStripRegularity W γ)
    (hm : UnitMomentMartingale (μ := W.μ) W.realFiltration (fun t ω ↦ gradient W γ t (X t ω)))
    {U : W.Ω → ℝ} (hUm : StronglyMeasurable[W.realFiltration 1] U)
    (hU : ∀ᵐ ω ∂W.μ, |U ω|≤1 ∧
      Tendsto (fun n ↦ gradient W γ (terminalTime n) (X (terminalTime n) ω)) atTop (𝓝 (U ω))) :
    Tendsto (fun T ↦ ∫ t in (0 : ℝ)..T, ∫ ω, curvature W γ t (X t ω) ∂W.μ)
      (𝓝[<] (1 : ℝ)) (𝓝 (∫ ω, U ω*W.B 1 ω ∂W.μ)) := by
  have hUs : AEStronglyMeasurable U W.μ := (hUm.mono (W.realFiltration.le 1)).aestronglyMeasurable
  apply (bounded_multiplier_integral_tendsto hUs (hU.mono (fun _ hω ↦ hω.1))
    (Eventually.of_forall (fun t : ℝ ↦ ((W.brownian.hasLaw_eval t.toNNReal).hasGaussianLaw.memLp (p := 1) (by norm_num)).integrable le_rfl))
    (((W.brownian.hasLaw_eval 1).hasGaussianLaw.memLp (p := 1) (by norm_num)).integrable le_rfl) W.L1_terminal).congr'
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ)<1)] with T hT
  exact hX.terminal_brownian_covariance hreg hm hUm hU hT.1 hT.2

end SKValue

end

end OAI
