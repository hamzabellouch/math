import OAI.Analysis.CircleDomains.Sobolev.ScalarRegularCoarea
import OAI.Analysis.CircleDomains.Sobolev.DifferentiableCriticalFibers
import OAI.Analysis.CircleDomains.Sobolev.LipschitzNullFibers

namespace OAI

/-! Exact weighted scalar coarea for a planar Lipschitz function. Regular
pieces, zero-derivative pieces, and the Rademacher null set are all included. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma weighted_coarea_of_zero_fibers {f : ℂ → ℝ} {A : Set ℂ} {q : ℂ → ℝ≥0∞}
    (hzero : ∀ᵐ t, (μH[1] : Measure ℂ) (A ∩ f ⁻¹' {t}) = 0)
    (henergy : (∫⁻ z in A, q z*ENNReal.ofReal ‖fderiv ℝ f z‖) = 0) :
    WeightedScalarCoareaIdentity A f q := by
  have he : weightedScalarLevelLength A f q =ᵐ[volume] fun _ => 0 := by
    filter_upwards [hzero] with t ht
    change (∫⁻ z in A ∩ {z | f z = t}, q z ∂μH[1]) = 0
    rw [show A ∩ {z | f z = t} = A ∩ f ⁻¹' {t} from rfl,
      Measure.restrict_eq_zero.mpr ht]
    exact lintegral_zero_measure q
  exact ⟨aemeasurable_const.congr he.symm, by rw [lintegral_congr_ae he, lintegral_zero, henergy]⟩

lemma lipschitz_scalar_weighted_coarea {f : ℂ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {E : Set ℂ} (hE : MeasurableSet E) (hb : IsBounded E)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) : WeightedScalarCoareaIdentity E f q := by
  let D := {z | DifferentiableAt ℝ f z}
  let R := (E ∩ D) ∩ {z | fderiv ℝ f z ≠ 0}
  let C := (E ∩ D) ∩ {z | fderiv ℝ f z = 0}
  let N := E \ D
  have hD : MeasurableSet D := measurableSet_of_differentiableAt ℝ f
  have hz : MeasurableSet {z | fderiv ℝ f z = 0} :=
    measurableSet_eq_fun (measurable_fderiv ℝ f) measurable_const
  have hR : MeasurableSet R := (hE.inter hD).inter hz.compl
  have hC : MeasurableSet C := (hE.inter hD).inter hz
  have hN : MeasurableSet N := hE.diff hD
  have hRco := scalar_regular_weighted_coarea hf.continuous hR
    (hb.subset (inter_subset_left.trans inter_subset_left)) (fun z hz => hz.1.2)
    (fun _ hz => hz.2) hq
  have hCzero := ae_zero_differentiable_critical_fiber_length hC
    (bounded_plane_hausdorff_two_lt_top (hb.subset (inter_subset_left.trans inter_subset_left)))
    (fun z hz => hz.1.2) (fun _ hz => hz.2)
  have hCenergy : (∫⁻ z in C, q z*ENNReal.ofReal ‖fderiv ℝ f z‖) = 0 := by
    apply setLIntegral_eq_zero hC
    intro z hz
    change q z*ENNReal.ofReal ‖fderiv ℝ f z‖ = 0
    rw [hz.2, norm_zero, ENNReal.ofReal_zero, mul_zero]
  have hCco := weighted_coarea_of_zero_fibers hCzero hCenergy
  have hNzero : volume N = 0 := by
    apply measure_mono_null (show N ⊆ Dᶜ from fun _ hz => hz.2)
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hf.ae_differentiableAt] with z hz
    exact fun hn => hn hz
  have hNenergy : (∫⁻ z in N, q z*ENNReal.ofReal ‖fderiv ℝ f z‖) = 0 := by
    rw [Measure.restrict_eq_zero.mpr hNzero]
    exact lintegral_zero_measure _
  have hNco := weighted_coarea_of_zero_fibers (lipschitz_null_fibers hf hNzero) hNenergy
  have hRC : Disjoint R C := by
    apply disjoint_left.mpr
    exact fun _ hr hc => hr.2 hc.2
  have heRC : R ∪ C = E ∩ D := by ext z; simp [R,C]; tauto
  have hED := weighted_coarea_union hf.continuous hC hRC q hRco hCco
  rw [heRC] at hED
  have hdEN : Disjoint (E ∩ D) N := by
    apply disjoint_left.mpr
    exact fun _ hd hn => hn.2 hd.2
  have heE : (E ∩ D) ∪ N = E := inter_union_sdiff E D
  have hh := weighted_coarea_union hf.continuous hN hdEN q hED hNco
  rwa [heE] at hh

end CircleDomainRigidity

end

end OAI
