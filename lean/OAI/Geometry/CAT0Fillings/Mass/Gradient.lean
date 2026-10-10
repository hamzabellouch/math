import Mathlib
import OAI.Geometry.CAT0Fillings.Slicing.NormalRestriction
import OAI.Geometry.CAT0Fillings.Gradient.HilbertAtlas
import OAI.Geometry.CAT0Fillings.Mass.Convolution

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal BigOperators

namespace CAT0Fillings
namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

theorem ae_coarea_mass_le_gradient {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) {S : ℝ → Functional X k}
    (hS : ∀ᵐ t : ℝ, IsMetricCurrent (S t))
    (hact : ∀ b π, Admissible b π → Integrable (fun t : ℝ => S t b π) ∧
      T b (Matrix.vecCons u π) = ∫ t : ℝ, S t b π)
    (hweight : ∀ b π, Admissible b π → ∀ φ : ℝ → ℝ, BoundedLip (φ ∘ u) →
      ∀ᵐ t : ℝ, S t (fun x => φ (u x)*b x) π = φ t * S t b π) :
    ∀ᵐ t : ℝ, mass (S t) ≤ (((q.gradientMeasure u).map u).rnDeriv volume t).toReal := by
  let := q.gradientMeasure_finite hu
  have hub : BoundedLip u := ⟨⟨K,hu⟩,by
    obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hu.continuous.continuousOn
    exact ⟨M,fun x => by simpa only [Real.norm_eq_abs] using hM x (mem_univ _)⟩⟩
  apply BorelCoefficients.ae_mass_le_of_listwise volume hS
  intro N b π hb hbudget hπ
  have hab i : Admissible (b i) (π i) := ⟨hb i,fun j => ⟨1,hπ i j⟩⟩
  have hi : Integrable (fun t => ∑ i, S t (b i) (π i)) :=
    integrable_finsetSum _ (fun i _ => (hact _ _ (hab i)).1)
  filter_upwards [SmoothCutoff.ae_tendsto_dprofile_integral hi,
    SmoothCutoff.ae_tendsto_dprofile_measure ((q.gradientMeasure u).map u)] with t ht hγ
  have hle (n : ℕ) : (∫ s : ℝ, SmoothCutoff.dprofile ((n:ℝ≥0)+1) t s *
      (∑ i, S s (b i) (π i))) ≤
      ∫ s, SmoothCutoff.dprofile ((n:ℝ≥0)+1) t s ∂(q.gradientMeasure u).map u := by
    let φ := SmoothCutoff.dprofile ((n:ℝ≥0)+1) t
    have hφ : BoundedLip (φ ∘ u) := Slicing.dprofile_comp_boundedLip hub _ t
    have hφ0 x : 0 ≤ φ x := mul_nonneg (NNReal.coe_nonneg _)
      Real.smoothTransition.monotone.deriv_nonneg
    have heq i : T (fun x => φ (u x)*b i x) (Fin.cons u (π i)) =
        ∫ s : ℝ, φ s * S s (b i) (π i) := by
      change T (fun x => (φ ∘ u) x*b i x) (Matrix.vecCons u (π i)) = _
      rw [(hact _ _ ⟨hφ.mul (hb i),(hab i).2⟩).2]
      exact integral_congr_ae (hweight _ _ (hab i) φ hφ)
    calc
      _ = ∑ i, ∫ s : ℝ, φ s * S s (b i) (π i) := by
        simp_rw [Finset.mul_sum]
        exact integral_finsetSum _ (fun i _ => SmoothCutoff.dprofile_mul_integrable (hact _ _ (hab i)).1 _ _)
      _ = ∑ i, T (fun x => φ (u x)*b i x) (Fin.cons u (π i)) := by simp_rw [heq]
      _ ≤ |∑ i, T (fun x => φ (u x)*b i x) (Fin.cons u (π i))| := le_abs_self _
      _ ≤ ∫ x, |φ (u x)| ∂q.gradientMeasure u :=
        q.list_action_le_gradient hu hφ b hb hbudget π hπ
      _ = ∫ x, φ (u x) ∂q.gradientMeasure u := by
        simp only [abs_of_nonneg (hφ0 _)]
      _ = _ := (integral_map hu.continuous.measurable.aemeasurable
        (SmoothCutoff.dprofile_integrable_measure ((q.gradientMeasure u).map u) _ _).aestronglyMeasurable).symm
  exact le_of_tendsto_of_tendsto ht hγ (Eventually.of_forall hle)

end ChartGeometry
end CAT0Fillings
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal BigOperators

namespace CAT0Fillings

lemma densityPush_add_of_nonneg {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {φ : α → β} (hφ : Measurable φ) {ρ σ : α → ℝ}
    (hρm : AEMeasurable ρ μ) (hρ : 0 ≤ᵐ[μ] ρ) (hσ : 0 ≤ᵐ[μ] σ) :
    densityPush μ φ (fun z => ρ z+σ z) = densityPush μ φ ρ + densityPush μ φ σ := by
  have hwd : μ.withDensity (fun z => ENNReal.ofReal (ρ z+σ z)) =
      μ.withDensity (fun z => ENNReal.ofReal (ρ z)) +
        μ.withDensity (fun z => ENNReal.ofReal (σ z)) := by
    apply Measure.ext
    intro s hs
    simp only [withDensity_apply _ hs,Measure.add_apply]
    calc
      _ = ∫⁻ z in s, ENNReal.ofReal (ρ z)+ENNReal.ofReal (σ z) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_of_ae hρ,ae_restrict_of_ae hσ] with z hz hzs
        exact ENNReal.ofReal_add hz hzs
      _ = _ := lintegral_add_left' (hρm.ennreal_ofReal.restrict) _
  simp only [densityPush,hwd,Measure.map_add _ _ hφ]

lemma weighted_young_real (c ρ d e : ℝ) (hρ : 0 ≤ ρ) (he : d^2 = e) :
    (2*c)*(ρ*d) ≤ c^2*ρ+ρ*e := by
  rw [←he]
  nlinarith [mul_nonneg hρ (sq_nonneg (c-d))]

lemma densityPush_quadratic_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {φ : α → β} (hφ : Measurable φ) (ρ d e : α → ℝ)
    (hρm : AEMeasurable ρ μ) (hρ : ∀ z, 0 ≤ ρ z)
    (hd : ∀ᵐ z ∂μ, d z^2 = e z) (c : ℝ≥0) :
    (2*c) • densityPush μ φ (fun z => ρ z*d z) ≤
      c^2 • densityPush μ φ ρ + densityPush μ φ (fun z => ρ z*e z) := by
  have hpoint : (fun z => (2*(c:ℝ))*(ρ z*d z)) ≤ᵐ[μ]
      (fun z => (c:ℝ)^2*ρ z + ρ z*e z) :=
    hd.mono fun z hz => weighted_young_real _ _ _ _ (hρ z) hz
  have hi := densityPush_mono_ae hφ hpoint
  have hadd : densityPush μ φ (fun z => (c:ℝ)^2*ρ z + ρ z*e z) =
      densityPush μ φ (fun z => (c:ℝ)^2*ρ z) + densityPush μ φ (fun z => ρ z*e z) :=
    densityPush_add_of_nonneg hφ (hρm.const_mul _)
      (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (hρ z))
      (hd.mono fun z hz => mul_nonneg (hρ z) (hz ▸ sq_nonneg (d z)))
  rw [hadd] at hi
  have hl : densityPush μ φ (fun z => (2*(c:ℝ))*(ρ z*d z)) =
      (2*c) • densityPush μ φ (fun z => ρ z*d z) := by
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using
      densityPush_const_mul μ φ (fun z => ρ z*d z) (2*c) hφ
  have hr : densityPush μ φ (fun z => (c:ℝ)^2*ρ z) =
      c^2 • densityPush μ φ ρ := by
    simpa only [NNReal.coe_pow] using densityPush_const_mul μ φ ρ (c^(2:ℕ)) hφ
  rwa [hl,hr] at hi

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X k}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma chart_gradient_quadratic_le (i : ℕ) {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) (c : ℝ≥0) :
    (2*c) • densityPush (volume.restrict (q.chart i).domain) (q.chart i).paramExtended
      (fun z => q.density i z*q.duNorm i u z) ≤
    c^2 • densityPush (volume.restrict (q.chart i).domain) (q.chart i).paramExtended
      (q.density i) +
    densityPush (volume.restrict (q.chart i).domain) (q.chart i).paramExtended
      (fun z => q.density i z*q.normSq i u z) :=
  densityPush_quadratic_le (q.chart i).measurable_paramExtended _ _ _
    (q.density_integrable i).aestronglyMeasurable.aemeasurable (q.density_nonneg i)
    ((q.ae_duNorm_bounds i hu).mono fun _ hz => hz.2.2) c

lemma gradient_quadratic_le {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    (c : ℝ≥0) : (2*c) • q.gradientMeasure u ≤
      c^2 • MassMeasure.currentMassMeasure hT + q.energyMeasure u := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.add_apply,Measure.smul_apply,Measure.smul_apply,q.measure_eq]
  simp only [gradientMeasure,energyMeasure,weightedMeasure,Measure.sum_apply _ hs]
  change (2*(c:ℝ≥0∞)) * _ ≤ (c:ℝ≥0∞)^2 * _ + _
  rw [←ENNReal.tsum_mul_left,←ENNReal.tsum_mul_left,←ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro i
  exact q.chart_gradient_quadratic_le i hu c s

end ChartGeometry
end CAT0Fillings
end

end OAI
