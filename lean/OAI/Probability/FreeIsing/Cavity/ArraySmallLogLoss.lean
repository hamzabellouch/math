import OAI.Probability.FreeIsing.Cavity.Array
import OAI.Probability.FreeIsing.Estimates.CoupledSmallLogLoss

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.CavityArray

variable {d : ℕ} {theta : ℝ}

theorem field_identDistrib_of_measurePreserving
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {μ : Measure (TreeVertex d → ℝ)} {F : Ω → (TreeVertex d → ℝ)}
    (hF : MeasurePreserving F ν μ) (h0 : 0 ≤ theta) (h1 : theta < 1)
    (v w : TreeVertex d) :
    IdentDistrib (fun ω => field h0 h1 (F ω) v w)
      (fun H => field h0 h1 H v w) ν μ := by
  have hm := measurable_field_apply h0 h1 v w
  refine ⟨(hm.comp hF.measurable).aemeasurable, hm.aemeasurable, ?_⟩
  rw [show (fun ω => field h0 h1 (F ω) v w) =
    (fun H => field h0 h1 H v w) ∘ F from rfl,
    ← Measure.map_map hm hF.measurable, hF.map_eq]

theorem integrable_site_sub_sq_of_bound
    {ν : Measure (SitePair d)} [IsProbabilityMeasure ν]
    {M : ℝ} (hM : 0 ≤ M) (v : TreeVertex d)
    (hbound : ∀ᵐ p ∂ν, |p.1 v - p.2 v| ≤ M) :
    Integrable (fun p : SitePair d => (p.1 v - p.2 v) ^ 2) ν := by
  apply (integrable_const (M ^ 2)).mono'
    ((((measurable_pi_apply v).comp measurable_fst).sub
      ((measurable_pi_apply v).comp measurable_snd)).pow_const 2).aestronglyMeasurable
  filter_upwards [hbound] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs, Function.comp_apply, Pi.sub_apply] using
    (sq_le_sq₀ (abs_nonneg _) hM).2 hp

theorem integral_log_field_sub_sq_le
    {ν : Measure (SitePair d)}
    (h0 : 0 ≤ theta) (h1 : theta < 1)
    (hinv : ∀ g : TreeAut d, MeasurePreserving (pairRelabel g) ν ν)
    (o v w : TreeVertex d)
    (hInt : Integrable (fun p : SitePair d => (p.1 o - p.2 o) ^ 2) ν) :
    (∫ p, (Real.log (responseAttenuation theta (field h0 h1 p.1 v w)) -
        Real.log (responseAttenuation theta (field h0 h1 p.2 v w))) ^ 2 ∂ν) ≤
      cavityLogVarianceCoefficient theta *
        (∫ p : SitePair d, (p.1 o - p.2 o) ^ 2 ∂ν) := by
  have hv := (site_sub_identDistrib hinv o v).sq
  have hw := (site_sub_identDistrib hinv o w).sq
  exact integral_cavity_log_discrepancy_sq_le h0 h1
    ((measurable_field_apply h0 h1 v w).comp measurable_fst)
    ((measurable_field_apply h0 h1 v w).comp measurable_snd)
    (hv.integrable_snd hInt) (hw.integrable_snd hInt)
    (Filter.Eventually.of_forall (fun p =>
      ⟨field_spec h0 h1 p.1 v w, field_spec h0 h1 p.1 w v,
        field_spec h0 h1 p.2 v w, field_spec h0 h1 p.2 w v⟩))
    hv.integral_eq.symm.le hw.integral_eq.symm.le

theorem integral_log_field_sub_sq_small_time
    {ν : Measure (SitePair d)} [IsProbabilityMeasure ν]
    {μ : Measure (TreeVertex d → ℝ)}
    (h0 : 0 ≤ theta) (h1 : theta < 1)
    (hinv : ∀ g : TreeAut d, MeasurePreserving (pairRelabel g) ν ν)
    (hfst : MeasurePreserving Prod.fst ν μ)
    (hsnd : MeasurePreserving Prod.snd ν μ)
    (o v w : TreeVertex d) {M t c : ℝ} (hM : 0 ≤ M) (ht : 0 < t)
    (hbound : ∀ᵐ p ∂ν, ∀ z : TreeVertex d, |p.1 z - p.2 z| ≤ M)
    (hTail : μ {H | t ^ (1 / 8 : ℝ) < |field h0 h1 H v w|} ≤
      ENNReal.ofReal (Real.exp (-c * (Real.log (1 / t)) ^ 2))) :
    (∫ p, (Real.log (responseAttenuation theta (field h0 h1 p.1 v w)) -
        Real.log (responseAttenuation theta (field h0 h1 p.2 v w))) ^ 2 ∂ν) ≤
      cavityLogVarianceCoefficient theta * t ^ (1 / 4 : ℝ) *
        (∫ p : SitePair d, (p.1 o - p.2 o) ^ 2 ∂ν) +
      min (cavityLogVarianceCoefficient theta *
        (∫ p : SitePair d, (p.1 o - p.2 o) ^ 2 ∂ν))
        (cavityLogTailCoefficient theta M * Real.exp (-c * (Real.log (1 / t)) ^ 2)) := by
  have hInt := integrable_site_sub_sq_of_bound hM o (hbound.mono (fun _ h => h o))
  have hv := (site_sub_identDistrib hinv o v).sq
  have hw := (site_sub_identDistrib hinv o w).sq
  exact integral_cavity_log_discrepancy_small_time_of_common_law h0 h1
    ((measurable_field_apply h0 h1 v w).comp measurable_fst)
    ((measurable_field_apply h0 h1 v w).comp measurable_snd)
    (hv.integrable_snd hInt) (hw.integrable_snd hInt)
    (Filter.Eventually.of_forall (fun p =>
      ⟨field_spec h0 h1 p.1 v w, field_spec h0 h1 p.1 w v,
        field_spec h0 h1 p.2 v w, field_spec h0 h1 p.2 w v⟩))
    hM ht (hbound.mono (fun _ h => ⟨h v, h w⟩))
    hv.integral_eq.symm.le hw.integral_eq.symm.le
    (field_identDistrib_of_measurePreserving hfst h0 h1 v w)
    (field_identDistrib_of_measurePreserving hsnd h0 h1 v w) hTail

end Problem367.CavityArray

end

end OAI
