import OAI.Analysis.CircleDomains.Rigidity.MaskedCoordinates
import OAI.Analysis.CircleDomains.Selection.UpperPairs

namespace OAI

/-!
# A common metric for coordinates on different masks

Only the actual masked covectors enter the wedge budget. Auxiliary
smooth coordinates agree with them outside the retained core, so the
resulting metric controls the sum of energies on the respective masks.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def maskedWedges {n : ℕ} (M : Fin n → Set (ℝ × ℝ))
    (f : Fin n → (ℝ × ℝ) → ℝ) (z : ℝ × ℝ) : ℝ :=
  ∑ p : UpperPairs n, |planarWedge
    (maskedGradient (M (upperPair p).1) (f (upperPair p).1) z)
    (maskedGradient (M (upperPair p).2) (f (upperPair p).2) z)|

theorem gradientEnergy_eq_indicator_of_maskedGradient
    {M : Set (ℝ × ℝ)} {F f : (ℝ × ℝ) → ℝ} {z : ℝ × ℝ}
    (hgrad : planarGradient F z = maskedGradient M f z)
    (g : (ℝ × ℝ) → PlanarMetric) :
    gradientEnergy F g z = M.indicator (gradientEnergy f g) z := by
  by_cases hz : z ∈ M
  · simpa only [maskedGradient, indicator_of_mem hz, gradientEnergy] using
      congrArg (fun v : ℝ × ℝ => covectorEnergy ![v.1, v.2] (g z)) hgrad
  · simp only [maskedGradient, indicator_of_notMem hz] at hgrad
    simp [gradientEnergy, hgrad, indicator_of_notMem hz, covectorEnergy]

/-- Small wedges of the actual masked differentials give one smooth
metric for all masks, with the prescribed total energy. -/
theorem exists_spherical_metric_for_masked_coordinates
    {n : ℕ} {Ω Q K : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (hK : IsClosed K) (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, IsClosed (M i))
    (hboundary : ∀ i, frontier (M i) ⊆ interior K)
    (f : Fin n → (ℝ × ℝ) → ℝ) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (Ω ∩ interior (M i)))
    {ε : ℝ} (hbudget : (∫ z in Q \ K, 2 * maskedWedges M f z) < ε) :
    ∃ (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric), 0 < R ∧ ContDiff ℝ ∞ g ∧
      (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
      (∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
      (∑ i : Fin n, ∫ z in (Q \ K) ∩ M i, gradientEnergy (f i) g z) < ε := by
  obtain ⟨F, hF, hgrad⟩ := exists_smooth_masked_family hΩ hQ hQΩ M hM hboundary f hf
  have hFn : ∀ i, ContDiffOn ℝ ∞ (natCoordinateFamily F i) Ω :=
    contDiffOn_natCoordinateFamily (fun i => (hF i).contDiffOn)
  have hW {z : ℝ × ℝ} (hz : z ∈ Q \ K) :
      coordinateWedges (natCoordinateFamily F) n z = maskedWedges M f z := by
    rw [coordinateWedges_eq_sum_upperPairs]
    apply sum_congr rfl
    intro p _
    rw [hgrad _ z hz, hgrad _ z hz]
  have hbudget' : (∫ z in Q \ K, 2 * coordinateWedges (natCoordinateFamily F) n z) < ε := by
    have heq := setIntegral_congr_fun (μ := volume) (hQ.isClosed.measurableSet.diff hK.measurableSet)
      (fun z hz => congrArg (fun a : ℝ => 2 * a) (hW hz))
    exact heq.trans_lt hbudget
  obtain ⟨R, g, hR, hg, hPD, hcore, hfar, henergy⟩ :=
    exists_supported_spherical_metric_for_coordinates _ n hΩ hQ hQΩ hFn hK hbudget'
  refine ⟨R, g, hR, hg, hPD, hcore, hfar, ?_⟩
  have heq : (∫ z in Q \ K, matrixEnergy (coordinateGram (natCoordinateFamily F) n z) (g z)) =
      ∑ i : Fin n, ∫ z in (Q \ K) ∩ M i, gradientEnergy (f i) g z := by
    rw [integral_coordinateGram_eq_sum hΩ hQ hQΩ _ hFn n hg.continuous hPD, Finset.sum_range]
    apply sum_congr rfl
    intro i _
    simp only [natCoordinateFamily, dite_eq_left i.isLt]
    calc
      (∫ z in Q \ K, gradientEnergy (F i) g z) =
          ∫ z in Q \ K, (M i).indicator (gradientEnergy (f i) g) z :=
        setIntegral_congr_fun (hQ.isClosed.measurableSet.diff hK.measurableSet)
          (fun z hz => gradientEnergy_eq_indicator_of_maskedGradient (hgrad i z hz) g)
      _ = _ := setIntegral_indicator (hM i).measurableSet
  exact heq.symm.trans_lt henergy

end CircleDomainRigidity.FiniteTransfer

end

end OAI
