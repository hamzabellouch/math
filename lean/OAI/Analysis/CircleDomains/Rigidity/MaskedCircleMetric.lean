import OAI.Analysis.CircleDomains.Sobolev.CovectorMetric

namespace OAI

/-!
# One metric for masked periodic coordinates

The actual intrinsic differentials of the circle coordinates are used
throughout. Mask boundaries lie inside the retained core, so the masked
covectors extend smoothly across the portion on which the metric changes.
Their pairwise wedge budget controls the sum of energies on the masks.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def natCovectorFamily {n : ℕ} (v : Fin n → (ℝ × ℝ) → ℝ × ℝ) :
    ℕ → (ℝ × ℝ) → ℝ × ℝ := fun i => if hi : i < n then v ⟨i, hi⟩ else fun _ => 0

def maskedCircleWedges {n : ℕ} (M : Fin n → Set (ℝ × ℝ))
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle) (z : ℝ × ℝ) : ℝ :=
  ∑ p : UpperPairs n, |planarWedge
    ((M (upperPair p).1).indicator (circleGradient (f (upperPair p).1)) z)
    ((M (upperPair p).2).indicator (circleGradient (f (upperPair p).2)) z)|

theorem contDiff_natCovectorFamily
    {n : ℕ} {v : Fin n → (ℝ × ℝ) → ℝ × ℝ}
    (hv : ∀ i, ContDiff ℝ ∞ (v i)) (i : ℕ) :
    ContDiff ℝ ∞ (natCovectorFamily v i) := by
  by_cases hi : i < n
  · simpa only [natCovectorFamily, dite_eq_left hi] using hv ⟨i, hi⟩
  · simp only [natCovectorFamily, dite_eq_right hi]
    exact contDiff_const

theorem fieldWedges_eq_sum_upperPairs {n : ℕ}
    (v : Fin n → (ℝ × ℝ) → ℝ × ℝ) (z : ℝ × ℝ) :
    fieldWedges (natCovectorFamily v) n z =
      ∑ p : UpperPairs n, |planarWedge (v (upperPair p).1 z) (v (upperPair p).2 z)| := by
  rw [fieldWedges, covectorWedges_eq_sum_upperPairs]
  apply sum_congr rfl
  intro p _
  have h₁ := p.2.isLt.trans p.1.isLt
  have h₂ := p.1.isLt
  simp only [natCovectorFamily, dite_eq_left h₁, dite_eq_left h₂, upperPair,
    planarWedge, mul_comm]

theorem fieldEnergy_indicator (M : Set (ℝ × ℝ)) (v : (ℝ × ℝ) → ℝ × ℝ)
    (g : (ℝ × ℝ) → PlanarMetric) (z : ℝ × ℝ) :
    fieldEnergy (M.indicator v) g z = M.indicator (fieldEnergy v g) z := by
  by_cases hz : z ∈ M
  · simp only [fieldEnergy, indicator_of_mem hz]
  · simp [fieldEnergy, indicator_of_notMem hz, covectorEnergy]

/-- This is the masked metric step for genuine circle-valued
coordinates; no globally defined scalar potentials are assumed. -/
theorem exists_spherical_metric_for_masked_circles
    {n : ℕ} {Ω Q K : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (hK : IsClosed K) (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, IsClosed (M i))
    (hboundary : ∀ i, frontier (M i) ⊆ interior K)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ i, SmoothCircleOn (f i) (Ω ∩ interior (M i)))
    {ε : ℝ} (hbudget : (∫ z in Q \ K, 2 * maskedCircleWedges M f z) < ε) :
    ∃ (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric), 0 < R ∧ ContDiff ℝ ∞ g ∧
      (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
      (∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
      (∑ i : Fin n, ∫ z in (Q \ K) ∩ M i, fieldEnergy (circleGradient (f i)) g z) < ε := by
  choose V hV hgrad using fun i => exists_smooth_masked_covector
    hΩ hQ hQΩ (hM i) (hboundary i)
    (contDiffOn_circleGradient (hΩ.inter isOpen_interior) (hf i))
  have hVn := contDiff_natCovectorFamily hV
  have hW {z : ℝ × ℝ} (hz : z ∈ Q \ K) :
      fieldWedges (natCovectorFamily V) n z = maskedCircleWedges M f z := by
    rw [fieldWedges_eq_sum_upperPairs]
    apply sum_congr rfl
    intro p _
    rw [hgrad _ z hz, hgrad _ z hz]
  have hbudget' : (∫ z in Q \ K, 2 * fieldWedges (natCovectorFamily V) n z) < ε := by
    have heq := setIntegral_congr_fun (μ := volume) (hQ.isClosed.measurableSet.diff hK.measurableSet)
      (fun z hz => congrArg (fun a : ℝ => 2 * a) (hW hz))
    exact heq.trans_lt hbudget
  obtain ⟨R, g, hR, hg, hPD, hcore, hfar, henergy⟩ :=
    exists_spherical_metric_for_covectors _ n hVn hQ hK hbudget'
  refine ⟨R, g, hR, hg, hPD, hcore, hfar, ?_⟩
  have heq : (∫ z in Q \ K, matrixEnergy (fieldGram (natCovectorFamily V) n z) (g z)) =
      ∑ i : Fin n, ∫ z in (Q \ K) ∩ M i, fieldEnergy (circleGradient (f i)) g z := by
    rw [integral_fieldGram_eq_sum hQ _ (fun i => (hVn i).continuous) n hg.continuous hPD,
      Finset.sum_range]
    apply sum_congr rfl
    intro i _
    simp only [natCovectorFamily, dite_eq_left i.isLt]
    calc
      (∫ z in Q \ K, fieldEnergy (V i) g z) =
          ∫ z in Q \ K, (M i).indicator (fieldEnergy (circleGradient (f i)) g) z := by
        apply setIntegral_congr_fun (hQ.isClosed.measurableSet.diff hK.measurableSet)
        intro z hz
        rw [← fieldEnergy_indicator]
        exact congrArg (fun v : ℝ × ℝ => covectorEnergy ![v.1, v.2] (g z)) (hgrad i z hz)
      _ = _ := setIntegral_indicator (hM i).measurableSet
  exact heq.symm.trans_lt henergy

end CircleDomainRigidity.FiniteTransfer

end

end OAI
