import OAI.Probability.SLE.Stochastic.PlanarSamplingLimit
import OAI.Probability.SLE.Stochastic.PlanarDomainStops

namespace OAI

/-! Conditional harmonic sampling on the actual compact domain stops. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

theorem planar_local_harmonic_optional_between
    (W : WienerLaw) (hW : IsWiener W) (U K : Set (ℝ×ℝ))
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (u : ℝ×ℝ → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hhar : ∀ z∈U, planarGenerator u z=0)
    (σ τ : Driver×Driver → ℝ≥0)
    (hσ : IsStoppingTime planarWienerFiltration (fun b => (σ b : WithTop ℝ≥0)))
    (hτ : IsStoppingTime planarWienerFiltration (fun b => (τ b : WithTop ℝ≥0)))
    (hστ : ∀ b, σ b ≤ τ b) (T : ℝ≥0) (hb : ∀ b, τ b ≤ T)
    (A : Set (Driver×Driver)) (hA : MeasurableSet[hσ.measurableSpace] A)
    (hpath : ∀ b t, t ≤ τ b → planarWiener t b∈K) :
    (∫ b in A, u (planarWiener (σ b) b) ∂W.prod W)=
      ∫ b in A, u (planarWiener (τ b) b) ∂W.prod W := by
  obtain ⟨f,hf,hfc,_,he,_,_⟩ := exists_compact_smooth_extension U K hU hK hKU u hu
  have hzero (b : Driver×Driver) (v : ℝ) (_hv : 0 ≤ v) (hvτ : v<(τ b:ℝ)) :
      planarGenerator f (planarWiener v.toNNReal b)=0 := by
    have ht : v.toNNReal ≤ τ b := Real.toNNReal_le_iff_le_coe.mpr hvτ.le
    have hz := hpath b v.toNNReal ht
    rw [planarGenerator_congr_germ (he _ hz)]
    exact hhar _ (hKU hz)
  have hh := planar_compact_optional_between W hW f hf hfc σ τ hσ hτ hστ T hb A hA hzero
  have ht (b) : f (planarWiener (τ b) b)=u (planarWiener (τ b) b) :=
    (he _ (hpath b (τ b) le_rfl)).self_of_nhds
  have hs (b) : f (planarWiener (σ b) b)=u (planarWiener (σ b) b) :=
    (he _ (hpath b (σ b) (hστ b))).self_of_nhds
  simpa only [ht,hs] using hh

namespace SmoothDomainExhaustion
variable {U : Set (ℝ×ℝ)} (e : SmoothDomainExhaustion U 0)

def stopFiltration (T : ℝ≥0) : Filtration ℕ (inferInstance : MeasurableSpace (Driver×Driver)) where
  seq n := (e.stop_stopping T n).measurableSpace
  mono' := fun n m hnm => (e.stop_stopping T n).measurableSpace_mono (e.stop_stopping T m)
    (fun b => WithTop.coe_le_coe.mpr (e.stop_monotone T b hnm))
  le' n := (e.stop_stopping T n).measurableSpace_le

lemma harmonic_stopped_adapted (T : ℝ≥0) (hU : IsOpen U)
    (u : ℝ×ℝ → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) :
    StronglyAdapted (e.stopFiltration T) (fun n b => u (planarWiener (e.stop T n b) b)) := by
  intro n
  obtain ⟨f,hf,_,_,he,_,_⟩ := exists_compact_smooth_extension U (tsupport (e.cutoff n))
    hU (e.compact n) (e.supported n) u hu
  have hb := measurable_stoppedValue ((Filtration.stronglyAdapted_natural (fun t =>
    (measurable_planarWiener t).stronglyMeasurable)).isStronglyProgressive_of_continuous
      planarWiener_continuous) (e.stop_stopping T n)
  have hm := hf.continuous.measurable.comp hb
  have heq (b) : f (planarWiener (e.stop T n b) b)=u (planarWiener (e.stop T n b) b) :=
    (he _ (e.stop_mem_support T n b _ le_rfl)).self_of_nhds
  change Measurable[(e.stopFiltration T) n] (fun b => f (planarWiener (e.stop T n b) b)) at hm
  simpa only [heq] using hm.stronglyMeasurable

theorem harmonic_stopped_martingale
    (W : WienerLaw) (hW : IsWiener W) (T : ℝ≥0) (hU : IsOpen U)
    (u : ℝ×ℝ → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hhar : ∀ z∈U, planarGenerator u z=0)
    (C : ℝ≥0) (huC : ∀ z∈U, |u z|≤C) :
    Martingale (fun n b => u (planarWiener (e.stop T n b) b)) (e.stopFiltration T) (W.prod W) := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  have ha := e.harmonic_stopped_adapted T hU u hu
  apply martingale_of_setIntegral_eq_succ ha
  · intro n
    exact Integrable.of_bound ((ha n).mono ((e.stopFiltration T).le n)).aestronglyMeasurable C
      (Eventually.of_forall fun b => by
        simpa only [Real.norm_eq_abs] using huC _ (e.stop_mem_domain T n b _ le_rfl))
  · intro n A hA
    exact planar_local_harmonic_optional_between W hW U (tsupport (e.cutoff (n+1)))
      hU (e.compact (n+1)) (e.supported (n+1)) u hu hhar (e.stop T n) (e.stop T (n+1))
      (e.stop_stopping T n) (e.stop_stopping T (n+1)) (fun b => e.stop_monotone T b (Nat.le_succ n))
      T (e.stop_le T (n+1)) A hA (e.stop_mem_support T (n+1))

theorem harmonic_stopped_converges
    (W : WienerLaw) (hW : IsWiener W) (T : ℝ≥0) (hU : IsOpen U)
    (u : ℝ×ℝ → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hhar : ∀ z∈U, planarGenerator u z=0)
    (C : ℝ≥0) (huC : ∀ z∈U, |u z|≤C) :
    ∀ᵐ b ∂W.prod W, ∃ c : ℝ, Tendsto (fun n => u (planarWiener (e.stop T n b) b)) atTop (𝓝 c) := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  have hm := e.harmonic_stopped_martingale W hW T hU u hu hhar C huC
  apply hm.submartingale.exists_ae_tendsto_of_bdd (R := C)
  intro n
  have hb : ∀ᵐ b ∂W.prod W, ‖u (planarWiener (e.stop T n b) b)‖ ≤ C :=
    Eventually.of_forall fun b => by
      simpa only [Real.norm_eq_abs] using huC _ (e.stop_mem_domain T n b _ le_rfl)
  simpa using eLpNorm_le_of_ae_bound (p := 1)
    (((hm.1 n).mono ((e.stopFiltration T).le n)).aestronglyMeasurable) hb

end SmoothDomainExhaustion
end SLEExactGauge

end

end OAI
