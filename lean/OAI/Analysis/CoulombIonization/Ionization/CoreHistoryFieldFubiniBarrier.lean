import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.CoreHistoryFieldBarrier
import OAI.Analysis.CoulombIonization.FieldAnalysis.CoreSubmeanSquareBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators

namespace CoulombAtom

lemma coreFieldSquare_joint_aestronglyMeasurable_of_aemeasurable
    {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (Z lam : ℝ) {μ : Measure Space}
    (hkernel : AEMeasurable
      (fun point : Configuration M => Measure.map (Prod.mk point) μ) volume) :
    AEStronglyMeasurable
      (fun q : Configuration M × Space => coreFieldSquare Z lam q.2 (coreSlice ψ t q.1))
      (volume.prod μ) := by
  have hfst : Measure.QuasiMeasurePreserving
      (Prod.fst : Configuration M × Space → Configuration M) (volume.prod μ) volume := by
    refine ⟨measurable_fst, Measure.AbsolutelyContinuous.mk fun subset hsubset hzero => ?_⟩
    rw [Measure.map_apply measurable_fst hsubset, Measure.prod,
      Measure.bind_apply (measurable_fst hsubset) hkernel]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with point hpoint
    rw [Measure.map_apply measurable_prodMk_left (measurable_fst hsubset)]
    have hempty : Prod.mk point ⁻¹' (Prod.fst ⁻¹' subset) = (∅ : Set Space) := by
      ext other
      simp [hpoint]
    rw [hempty, measure_empty]
    rfl
  obtain ⟨F,hF,he⟩ := coreSlice_field_measurable_rep hψ t Z lam
  have hh : AEStronglyMeasurable (fun q : Configuration M × Space =>
      (max (F q) 0)^2*formMass (coreSlice ψ t q.1)) (volume.prod μ) :=
    ((hF.max measurable_const).pow_const 2).aestronglyMeasurable.mul
    ((hψ.coreSlice_mass_integrable t).aestronglyMeasurable.comp_quasiMeasurePreserving hfst)
  apply hh.congr
  filter_upwards [hfst.ae he] with q hq
  rw [hq q.2]
  rfl

lemma coreFieldSquare_joint_aestronglyMeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (Z lam : ℝ) {μ : Measure Space} [SFinite μ] :
    AEStronglyMeasurable
      (fun q : Configuration M × Space => coreFieldSquare Z lam q.2 (coreSlice ψ t q.1))
      (volume.prod μ) :=
  coreFieldSquare_joint_aestronglyMeasurable_of_aemeasurable hψ t Z lam
    Measurable.map_prodMk_left.aemeasurable

lemma coreFieldSquare_weighted_prod_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) {Z lam d : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hd : 0 < d) {w : Space → ℝ}
    (hw : Integrable w) (hn : ∀ z, 0 ≤ w z) (hs : ∀ z, w z ≠ 0 → d ≤ ‖z‖) :
    Integrable (fun q : Configuration M × Space =>
      coreFieldSquare Z lam q.2 (coreSlice ψ t q.1)*w q.2) (volume.prod volume) := by
  have hi := ((hψ.coreSlice_mass_integrable t).mul_prod hw).const_mul ((Z/d)^2)
  apply hi.mono' ((coreFieldSquare_joint_aestronglyMeasurable hψ t Z lam).mul
    hw.aestronglyMeasurable.comp_snd)
  apply ae_of_all
  intro q
  change ‖coreFieldSquare Z lam q.2 (coreSlice ψ t q.1)*w q.2‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (coreFieldSquare_nonneg _ _ _ _) (hn _))]
  by_cases he : w q.2 = 0
  · simp only [he,mul_zero,le_refl]
  · have hb := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (le_max_right _ _) (normalizedCoreField_pos_le
        (coreSlice ψ t q.1) hZ hlam hd (hs q.2 he)) 2)
      (formMass_nonneg (coreSlice ψ t q.1))
    have hh := mul_le_mul_of_nonneg_right hb (hn q.2)
    simpa only [coreFieldSquare,mul_assoc] using hh

lemma coreFieldSquare_weighted_fubini {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z lam : ℝ) {d : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hd : 0 < d) {w : Space → ℝ}
    (hw : Integrable w) (hn : ∀ z, 0 ≤ w z) (hs : ∀ z, w z ≠ 0 → d ≤ ‖z‖) :
    coreLawAverage ψ (fun φ => ∫ z, coreFieldSquare Z lam z φ*w z) =
      ∫ z, coreLawAverage ψ (coreFieldSquare Z lam z)*w z := by
  unfold coreLawAverage
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro t _
    rw [integral_integral_swap (coreFieldSquare_weighted_prod_integrable hψ t hZ hlam hd hw hn hs)]
    apply integral_congr_ae
    exact ae_of_all _ (fun z => integral_mul_const (w z) _)
  · intro t _
    have hi := (coreFieldSquare_weighted_prod_integrable hψ t hZ hlam hd hw hn hs).integral_prod_right
    simpa only [integral_mul_const] using hi

namespace CoreObservationGraph

lemma fieldMoment_weighted_integrable (G : CoreObservationGraph) {Z lam d : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hd : 0 < d) {w : Space → ℝ}
    (hw : Integrable w) (hn : ∀ z, 0 ≤ w z) (hs : ∀ z, w z ≠ 0 → d ≤ ‖z‖) :
    Integrable (fun z => G.fieldMoment Z lam z*w z) := by
  unfold fieldMoment coreLawAverage
  simp only [Finset.sum_mul]
  apply integrable_finsetSum
  intro t _
  have hi := (coreFieldSquare_weighted_prod_integrable G.sobolev t hZ hlam hd hw hn hs).integral_prod_right
  simpa only [integral_mul_const] using hi

end CoreObservationGraph
end CoulombAtom

end

end OAI
