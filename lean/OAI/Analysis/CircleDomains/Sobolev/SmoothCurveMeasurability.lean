import OAI.Analysis.CircleDomains.Sobolev.SmoothCurveCoarea

namespace OAI

/-! Measurability of the actual differential-weighted curve fibers is
inherited from the published Lipschitz pieces and countable additivity. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem aemeasurable_smooth_curve_fiber
    (hcoarea : PlanarLipschitzFiberCoarea)
    {D A : Set ℂ} (hD : IsOpen D) (hA : MeasurableSet A) (hAD : A ⊆ D)
    (hfin : (μH[1] : Measure ℂ) A < ∞)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) :
    AEMeasurable (fun t => (μH[0] : Measure ℂ) (A ∩ f ⁻¹' {t})) volume := by
  obtain ⟨U, L, hU, hcover, _, hLip, _⟩ := exists_countable_derivative_cover hD hf zero_lt_one
  let E : ℕ → Set ℂ := fun n => A ∩ disjointed U n
  have hE (n : ℕ) : MeasurableSet (E n) :=
    hA.inter (MeasurableSet.disjointed (fun n => (hU n).measurableSet) n)
  have hEU (n : ℕ) : E n ⊆ U n := fun z hz => disjointed_subset U n hz.2
  have hEA (n : ℕ) : E n ⊆ A := inter_subset_left
  have hdisj : Pairwise (Disjoint on E) := by
    intro i j hij
    exact (disjoint_disjointed U hij).mono inter_subset_right inter_subset_right
  have hEq : (⋃ n, E n) = A := by
    ext z
    simp only [E, ← inter_iUnion, iUnion_disjointed, mem_inter_iff]
    exact ⟨And.left, fun hz => ⟨hz, hcover (hAD hz)⟩⟩
  have hm (n : ℕ) := (curve_coarea_lipschitzOn hcoarea (hE n)
    ((measure_mono (hEA n)).trans_lt hfin) ((hLip n).mono (hEU n))).1
  have hlevel (n : ℕ) (t : ℝ) : MeasurableSet (E n ∩ f ⁻¹' {t}) := by
    obtain ⟨g, hg, he⟩ := ((hLip n).mono (hEU n)).extend_real
    have heq : E n ∩ f ⁻¹' {t} = E n ∩ g ⁻¹' {t} := by
      ext z
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
      exact and_congr_right (fun hz => by rw [he hz])
    rw [heq]
    exact (hE n).inter (hg.continuous.measurable (measurableSet_singleton t))
  have heq : (fun t => (μH[0] : Measure ℂ) (A ∩ f ⁻¹' {t})) =
      (fun t => ∑' n, (μH[0] : Measure ℂ) (E n ∩ f ⁻¹' {t})) := by
    funext t
    rw [← hEq, iUnion_inter]
    apply measure_iUnion
    · intro i j hij
      exact (hdisj hij).mono inter_subset_left inter_subset_left
    · exact fun n => hlevel n t
  rw [heq]
  exact AEMeasurable.tsum hm

end CircleDomainRigidity

end

end OAI
