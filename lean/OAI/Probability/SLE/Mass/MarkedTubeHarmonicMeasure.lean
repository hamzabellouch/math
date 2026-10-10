import OAI.Probability.SLE.Geometry.MarkedWindowRoutes
import OAI.Probability.SLE.Geometry.FiniteExitArcAt

namespace OAI

/-! Convert the two explicit marked-point Brownian tubes into lower
bounds for both conformal exit arcs. Every geometric condition concerns
actual paths in the surviving domain; the only probabilistic input here
is the generic published conformal Brownian exit law. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Serpentine
open RibbonCoordinates CrosscutSides Target

lemma marked_window_tubes_opposite_sides
    (hopen : PublishedPlanarDiskOpenness) (w : ℂ) {a : ℝ} (ha : 0 < a)
    (f : ℂ → ℂ) (j : ℂ → ℝ)
    (hf : ContinuousOn f (ball (0 : ℂ) (a / 12)))
    (hfi : InjOn f (ball (0 : ℂ) (a / 12)))
    (hzero : ∀ z ∈ ball (0 : ℂ) (a / 12), (f z).re = 0 ↔ z.im = 0)
    (hrel : ∀ z ∈ ball (0 : ℂ) (a / 12), j (markedCornerChart w z) = (f z).re) :
    ∃ right : Bool,
      (∀ y : ℂ, dist y (markedWindowRoute right w a (1 / 64)) < a / 10000 → 0 < j y) ∧
      (∀ y : ℂ, dist y (markedWindowRoute (!right) w a (1 / 64)) < a / 10000 → j y < 0) := by
  rcases marked_physical_tubes_opposite_sides hopen w ha f j hf hfi hzero hrel with h | h
  · refine ⟨false, ?_⟩
    simpa only [markedWindowRoute_small, Bool.false_eq_true, ↓reduceIte, Bool.not_false] using h
  · refine ⟨true, ?_⟩
    simpa only [markedWindowRoute_small, ↓reduceIte, Bool.not_true, Bool.false_eq_true] using And.symm h

theorem marked_tubes_harmonic_bounds
    (hopen : PublishedPlanarDiskOpenness) (hexitLaw : PublishedHalfPlaneConformalExitLaw)
    (W : WienerLaw) (hW : IsWiener W)
    (D : Set ℂ) (hD : IsOpen D) (hDH : D ⊆ upperHalfPlane)
    (g F : ℂ → ℂ) (hg : DifferentiableOn ℂ g D)
    (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hgH : MapsTo g D upperHalfPlane) (hFD : MapsTo F upperHalfPlane D)
    (hFg : ∀ z ∈ D, F (g z) = z) (hgF : ∀ z ∈ upperHalfPlane, g (F z) = z)
    (w : ℂ) (hwD : w ∈ D) {a : ℝ} (ha : 0 < a)
    (h : ℂ ≃ₜ ℂ) (hreal : ∀ x : ℝ, h (x : ℂ) = (x : ℂ))
    (hloc : ContinuousOn (fun z => h (g (markedCornerChart w z))) (ball (0 : ℂ) (a / 12)))
    (hloci : InjOn (fun z => h (g (markedCornerChart w z))) (ball (0 : ℂ) (a / 12)))
    (hlocz : ∀ z ∈ ball (0 : ℂ) (a / 12),
      (h (g (markedCornerChart w z))).re = 0 ↔ z.im = 0)
    (q : ℝ≥0∞)
    (hprob : ∀ right : Bool, q ≤ (W.prod W) {b | ∀ t ∈ Icc (0 : ℝ) 3,
      dist (physicalUnitBrownianPath w b t) (markedWindowRoute right w a t) < a / 10000})
    (hgeom : ∀ (right : Bool) (b : Driver × Driver),
      (∀ t ∈ Icc (0 : ℝ) 3,
        dist (physicalUnitBrownianPath w b t) (markedWindowRoute right w a t) < a / 10000) →
      ∃ τ : ℝ, UnitWindowFirstExit D (physicalUnitBrownianPath w b) τ ∧ (1 / 64 : ℝ) < τ ∧
        ∀ t ∈ Ico (1 / 64 : ℝ) τ, (h (g (physicalUnitBrownianPath w b t))).re ≠ 0) :
    q ≤ ENNReal.ofReal ((g w).arg / Real.pi) ∧
      q ≤ ENNReal.ofReal (1 - (g w).arg / Real.pi) := by
  let E := fun right : Bool => {b | ∀ t ∈ Icc (0 : ℝ) 3,
    dist (physicalUnitBrownianPath w b t) (markedWindowRoute right w a t) < a / 10000}
  obtain ⟨hae, hnegBound, hposBound⟩ := hexitLaw W hW D g F hD hDH
    hg hF hgH hFD hFg hgF w hwD
  obtain ⟨right, hpos, hneg⟩ := marked_window_tubes_opposite_sides hopen w ha
    (fun z => h (g (markedCornerChart w z))) (fun z => (h (g z)).re)
    hloc hloci hlocz (fun _ _ => rfl)
  have hposProb : q ≤ (W.prod W) (unitWindowExitArc D g w 1) := by
    refine (hprob right).trans (finite_exit_event_measure_le_arc_at (W.prod W) D g w h hreal
      hg.continuousOn (E right) (Or.inr rfl) (by norm_num : (0 : ℝ) ≤ 1 / 64) hae
      (hgeom right) ?_)
    intro b hb
    simpa only [one_mul] using hpos _ (hb _ (by norm_num))
  have hnegProb : q ≤ (W.prod W) (unitWindowExitArc D g w (-1)) := by
    refine (hprob (!right)).trans (finite_exit_event_measure_le_arc_at (W.prod W) D g w h hreal
      hg.continuousOn (E (!right)) (Or.inl rfl) (by norm_num : (0 : ℝ) ≤ 1 / 64) hae
      (hgeom (!right)) ?_)
    intro b hb
    have hh := hneg _ (hb _ (by norm_num))
    nlinarith
  exact ⟨hnegProb.trans hnegBound, hposProb.trans hposBound⟩

/-- Early survival, a final exit and avoidance of the actual complete
guide imply the geometric hypotheses in the harmonic-measure theorem. -/
theorem marked_tube_first_exit_geometry
    (D : Set ℂ) (hD : IsOpen D) (g : ℂ → ℂ) (h : ℂ ≃ₜ ℂ)
    (α : ℝ≥0 → ℂ)
    (hzero : ∀ z ∈ D, (h (g z)).re = 0 → ∃ u : ℝ≥0, 0 < u ∧ α u = z)
    (ζ : ℝ → ℂ) (hc : Continuous ζ)
    (hearly : MapsTo ζ (Icc (0 : ℝ) (1 / 64)) D)
    (hlast : ζ 3 ∉ D)
    (havoid : ∀ t ∈ Icc (1 / 64 : ℝ) 3, ∀ u : ℝ≥0, 0 < u → ζ t ≠ α u) :
    ∃ τ : ℝ, UnitWindowFirstExit D ζ τ ∧ (1 / 64 : ℝ) < τ ∧
      ∀ t ∈ Ico (1 / 64 : ℝ) τ, (h (g (ζ t))).re ≠ 0 := by
  obtain ⟨τ, hτ, hout, hin⟩ := exists_first_domain_exit (L := 3) D hD ζ hc.continuousOn hearly
    ⟨3, by norm_num, hlast⟩
  refine ⟨τ, ⟨⟨by linarith [hτ.1], hτ.2⟩, hout, hin⟩, hτ.1, ?_⟩
  intro t ht he
  obtain ⟨u, hu, hue⟩ := hzero (ζ t) (hin ⟨by linarith [ht.1], ht.2⟩) he
  exact havoid t ⟨ht.1, ht.2.le.trans hτ.2⟩ u hu hue.symm

end SLEExactGauge.Serpentine

end

end OAI
