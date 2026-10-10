import Mathlib
import OAI.Geometry.IntegralFillings.Charts.Extensions

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings
open MeasureTheory

lemma densityPush_congr_ae {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    (μ : Measure Z) (φ : Z → X) {ρ σ : Z → ℝ} (h : ρ =ᵐ[μ] σ) :
    densityPush μ φ ρ = densityPush μ φ σ := by
  have hdensity : μ.withDensity (fun point => ENNReal.ofReal (ρ point)) =
      μ.withDensity (fun point => ENNReal.ofReal (σ point)) :=
    withDensity_congr_ae (h.fun_comp ENNReal.ofReal)
  unfold densityPush
  rw [hdensity]

lemma densityPush_restrict_le_restrict_image {Z X : Type*}
    [MeasurableSpace Z] [MeasurableSpace X]
    (μ : Measure Z) {φ : Z → X} (hφ : Measurable φ) (ρ : Z → ℝ)
    {t : Set Z} (ht : MeasurableSet t) (him : MeasurableSet (φ '' t)) :
    densityPush (μ.restrict t) φ ρ ≤ (densityPush μ φ ρ).restrict (φ '' t) := by
  simp only [densityPush_eq_map _ hφ]
  rw [←restrict_withDensity ht,Measure.restrict_map hφ him]
  apply Measure.map_mono _ hφ
  apply Measure.restrict_mono _ le_rfl
  intro x hx
  exact ⟨x,hx,rfl⟩

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)

lemma measurableSet_paramExtended_image {t : Set (Euc k)}
    (ht : MeasurableSet t) (hts : t ⊆ C.domain) :
    MeasurableSet (C.paramExtended '' t) := by
  let := ht.standardBorel
  have hi : Function.Injective (fun z : t => C.paramExtended (z : Euc k)) := by
    intro a b hab
    have hab' : C.param ⟨a,hts a.property⟩ = C.param ⟨b,hts b.property⟩ := by
      simpa only [paramExtended,dite_eq_left (hts a.property),dite_eq_left (hts b.property)] using hab
    obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
    apply Subtype.ext
    exact congrArg (fun z : C.domain => (z : Euc k)) (hU.injective hab')
  have hm := (C.measurable_paramExtended.comp measurable_subtype_coe).measurableEmbedding hi
  have heq : range (fun z : t => C.paramExtended (z : Euc k)) = C.paramExtended '' t := by
    ext x
    simp
  rw [←heq]
  exact hm.measurableSet_range

lemma linear_piece_mass_le
    (hC : IsMetricCurrent C.action) {ν : Measure X} [IsFiniteMeasure ν]
    (hν : Controls C.action ν) {t : Set (Euc k)}
    (ht : MeasurableSet t) (hts : t ⊆ C.domain)
    (ℓ : Fin k → Euc k →L[ℝ] ℝ) (K : ℝ≥0)
    (hrow : ∀ i y (hy : y ∈ t) z (hz : z ∈ t),
      |ℓ i y - ℓ i z| ≤ (K : ℝ)*dist (C.param ⟨y,hts hy⟩) (C.param ⟨z,hts hz⟩)) :
    densityPush (volume.restrict t) C.paramExtended
      (fun z => |(C.multiplicity z : ℝ)| *
        |(Matrix.of fun i j => ℓ i (EuclideanSpace.single j 1)).det|)
      ≤ ((K^k) • ν).restrict (C.paramExtended '' t) := by
  obtain ⟨π,hπ,_,hjac⟩ := C.exists_inverse_coordinate_tests ht hts ℓ K hrow
  have heq : densityPush (volume.restrict t) C.paramExtended
      (fun z => |(C.multiplicity z : ℝ)| *
        |(Matrix.of fun i j => ℓ i (EuclideanSpace.single j 1)).det|) =
      densityPush (volume.restrict t) C.paramExtended
        (fun z => |(C.multiplicity z : ℝ)*C.jacobian π z|) := by
    apply densityPush_congr_ae
    filter_upwards [hjac] with z hz
    rw [hz,abs_mul]
  rw [heq]
  have hrest : (volume.restrict C.domain).restrict t = volume.restrict t := by
    rw [Measure.restrict_restrict ht,inter_eq_left.mpr hts]
  calc
    _ = densityPush ((volume.restrict C.domain).restrict t) C.paramExtended
        (fun z => |(C.multiplicity z : ℝ)*C.jacobian π z|) := by rw [hrest]
    _ ≤ (densityPush (volume.restrict C.domain) C.paramExtended
        (fun z => |(C.multiplicity z : ℝ)*C.jacobian π z|)).restrict
          (C.paramExtended '' t) :=
      densityPush_restrict_le_restrict_image (volume.restrict C.domain)
        C.measurable_paramExtended _ ht (C.measurableSet_paramExtended_image ht hts)
    _ ≤ ((K^k) • ν).restrict (C.paramExtended '' t) := by
      apply Measure.restrict_mono le_rfl
      simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
        C.weighted_jacobian_le_measure hC hν π (fun _ => K) hπ

end IntegerChart
end SharpIntegralFillings

namespace SharpIntegralFillings
open MeasureTheory

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
  {k : ℕ} (C : IntegerChart X k)

noncomputable def majorantMeasure (J : Euc k → ℝ) : Measure X :=
  densityPush (volume.restrict C.domain) C.paramExtended
    (fun z => |(C.multiplicity z : ℝ)| * J z)

lemma majorant_controls {J : Euc k → ℝ}
    (hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| * J z) (volume.restrict C.domain))
    (hJ : 0 ≤ᵐ[volume.restrict C.domain] J)
    (hdet : ∀ π : Fin k → X → ℝ, (∀ i, LipschitzWith 1 (π i)) →
      ∀ᵐ z ∂volume.restrict C.domain, |C.jacobian π z| ≤ J z) :
    Controls C.action (C.majorantMeasure J) := by
  intro b π hb hπ
  let μ := volume.restrict C.domain
  have hbmeas := hb.continuous.measurable.comp C.measurable_paramExtended
  obtain ⟨M,hM⟩ := hb.2
  have hupper : Integrable (fun z => (|(C.multiplicity z : ℝ)| * J z)*|b (C.paramExtended z)|) μ :=
    hρ.mul_bdd hbmeas.abs.aestronglyMeasurable
      (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs,abs_abs] using hM _)
  have hρ0 : 0 ≤ᵐ[μ] fun z => |(C.multiplicity z : ℝ)| * J z :=
    hJ.mono fun z hz => mul_nonneg (abs_nonneg _) hz
  rw [majorantMeasure,integral_densityPush μ C.measurable_paramExtended hρ hρ0 hb.continuous.abs]
  rw [action,ite_eq_left ⟨hb,fun i => ⟨1,hπ i⟩⟩]
  rw [← Real.norm_eq_abs]
  apply le_trans (norm_integral_le_integral_norm _) ?_
  change (∫ z, |(C.multiplicity z : ℝ)*C.scalar b z*C.jacobian π z| ∂μ) ≤ _
  apply integral_mono_ae
    (C.integrable_action_integrand hb (fun i => ⟨1,hπ i⟩)).abs hupper
  filter_upwards [hdet π hπ,C.scalar_ae_paramExtended b] with z hz hbz
  rw [abs_mul,abs_mul,hbz]
  change |(C.multiplicity z : ℝ)| * |b (C.paramExtended z)| * |C.jacobian π z| ≤ _
  calc _ ≤ (|(C.multiplicity z : ℝ)| * |b (C.paramExtended z)|) * J z :=
      mul_le_mul_of_nonneg_left hz (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by ring

end IntegerChart
end SharpIntegralFillings

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

end

end OAI
