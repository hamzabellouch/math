import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CompactDetectorScalarTranslation

namespace OAI

/-! The analytic detector at an arbitrary center.  Its prescribed drift
and source are translations of the fixed-center program. The two numerical
choices use the same force. -/

noncomputable section
namespace ForcedComputation.VelocityDetector.CompactCenter
open ShearFlows Set
open scoped ContDiff

def centerShift (p : Plane) : Plane :=
  letI := ShearFlows.fourAtLeastTwo
  p - ![1 / 4, 1 / 4]

theorem reference_add_shift (p : Plane) : ![1 / 4, 1 / 4] + centerShift p = p := by
  unfold centerShift
  abel

theorem euclidean_translated (δ : Plane) (f : Plane → Plane) :
    euclideanMap (fun x => f (x + δ)) =
      fun x => euclideanMap f (x + planeCoordinates.symm δ) := by
  funext x
  simp only [euclideanMap, map_add, ContinuousLinearEquiv.apply_symm_apply]

theorem euclidean_translated_first (δ : Plane) (f : Plane → Plane) (x : EuclideanPlane) :
    fderiv ℝ (euclideanMap (fun y => f (y + δ))) x =
      fderiv ℝ (euclideanMap f) (x + planeCoordinates.symm δ) := by
  rw [euclidean_translated, fderiv_comp_add_right]

theorem euclidean_translated_second (δ : Plane) (f : Plane → Plane) (x : EuclideanPlane) :
    fderiv ℝ (fderiv ℝ (euclideanMap (fun y => f (y + δ)))) x =
      fderiv ℝ (fderiv ℝ (euclideanMap f)) (x + planeCoordinates.symm δ) := by
  have he : fderiv ℝ (euclideanMap (fun y => f (y + δ))) =
      fun y => fderiv ℝ (euclideanMap f) (y + planeCoordinates.symm δ) :=
    funext (euclidean_translated_first δ f)
  rw [he, fderiv_comp_add_right]

def centeredDrift (V : ℝ → Plane → Plane) (p : Plane) (C L : ℕ) : ℝ → Plane → Plane :=
  translateField (-centerShift p) (detectorDrift (translateField (centerShift p) V) C L)

def centeredSource (p : Plane) (C L : ℕ) : ℝ → Plane → ℝ :=
  translateField (-centerShift p) (detectorSource C L)

theorem centeredDrift_eq (V : ℝ → Plane → Plane) (p : Plane) (C L : ℕ) :
    centeredDrift V p C L = detectorDrift V C L := by
  funext t x
  unfold centeredDrift translateField detectorDrift detectorBlockSum
  apply tsum_congr
  intro n
  simp only [detectorDriftTerm, neg_add_cancel_right]

def centeredForce (V : ℝ → Plane → Plane) (p : Plane) (C L : ℕ) (ν : ℝ) : Velocity :=
  triangularForce ν (viscosityDrift ν (centeredDrift V p C L))
    (viscositySource ν (centeredSource p C L))

theorem general_center_compact_detector (hE : TorusScalarExistence) (hK : TorusHeatInput)
    {V : ℝ → Plane → Plane} {Ψ : ℝ → ℝ → Plane → Plane}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (hp : ∀ s, PlanePeriodic (V s))
    (hdiv : ∀ s x, PlanarHamiltonian.divergence (V s) x = 0)
    (hΨ : IsPlanarTransition V Ψ) (hv : PlanarVariations V Ψ)
    (hback : ContDiff ℝ ∞ (fun y : ℝ × Plane => Ψ y.1 (-y.1) y.2))
    (L : ℕ) (hL : 0 < L)
    (h₁ : ∀ s x, ‖fderiv ℝ (euclideanMap (V s)) x‖ ≤ (L : ℝ))
    (h₂ : ∀ s x, ‖fderiv ℝ (fderiv ℝ (euclideanMap (V s))) x‖ ≤ (L : ℝ))
    (p : Plane) :
    ∃ w : ℝ → Plane → ℝ,
      GlobalTorusScalarSolution 1 (centeredDrift V p detectorBumpDerivativeBound L)
        (centeredSource p detectorBumpDerivativeBound L) w (fun _ => 0) ∧
      ContDiff ℝ ∞ (Function.uncurry w) ∧ (∀ t x, 0 ≤ w t x) ∧
      (∀ t, 0 ≤ t → scalarMass w t ≤ (massBound L : ℝ)) ∧
      (massBound L : ℝ) < 1 / 100000000000 ∧
      ∀ ν : ℝ, 0 < ν →
        IsClassicalSolution 1 ν (centeredForce V p detectorBumpDerivativeBound L ν)
          (triangularVelocity
            (viscosityDrift ν (centeredDrift V p detectorBumpDerivativeBound L))
            (viscosityScalar ν w)) (fun _ => 0) ∧
        (∀ u q, IsClassicalSolution 1 ν (centeredForce V p detectorBumpDerivativeBound L ν) u q →
          ∀ t, 0 ≤ t → ∀ x, u (t, x) =
            triangularVelocity (viscosityDrift ν (centeredDrift V p detectorBumpDerivativeBound L))
              (viscosityScalar ν w) (t, x) ∧ q (t, x) = 0) ∧
        ∀ (E : Set Plane) (d H : ℝ), DetectorPair d H →
          ((∃ k : ℕ, Ψ 0 k p ∈ E) →
            ∃ t, 0 ≤ t ∧ ∃ x ∈ E, 1 / 2 < viscosityScalar ν w t x) ∧
          ((∀ s, 0 ≤ s → ∀ x ∈ E, 2 * d ≤ torusNorm (Ψ 0 s p - x)) →
            ∀ t, 0 ≤ t → ∀ x ∈ E, viscosityScalar ν w t x < 1 / 2) := by
  let δ := centerShift p
  let V' := translateField δ V
  let Ψ' := translateTransition δ Ψ
  have hV' : ContDiff ℝ ∞ (Function.uncurry V') := translated_smooth δ hV
  have hp' : ∀ s, PlanePeriodic (V' s) := translated_periodic δ hp
  have hd' : ∀ s x, PlanarHamiltonian.divergence (V' s) x = 0 := by
    intro s x
    rw [translated_divergence, hdiv]
  have h₁' : ∀ s x, ‖fderiv ℝ (euclideanMap (V' s)) x‖ ≤ (L : ℝ) := by
    intro s x
    rw [show V' s = (fun y => V s (y + δ)) from rfl, euclidean_translated_first]
    exact h₁ _ _
  have h₂' : ∀ s x, ‖fderiv ℝ (fderiv ℝ (euclideanMap (V' s))) x‖ ≤ (L : ℝ) := by
    intro s x
    rw [show V' s = (fun y => V s (y + δ)) from rfl, euclidean_translated_second]
    exact h₂ _ _
  obtain ⟨w₀, hs₀, _, _, hm₀, hsmall, hall⟩ := fixed_center_compact_detector hE hK hV' hp' hd'
    (transition_translated hΨ δ) (variations_translated hv δ) (backward_translated hback δ)
    L hL h₁' h₂'
  obtain ⟨v, hsv, hv', hvp, hnv, _⟩ := detectorScalar_exists hE hV' hp' detectorBumpDerivativeBound L
  have he (t : ℝ) (ht : 0 ≤ t) : v t = w₀ t := hsv.unique hs₀ (by norm_num) t ht
  let w := translateField (-δ) v
  have hw : ContDiff ℝ ∞ (Function.uncurry w) := translated_smooth (-δ) hv'
  have hwp : ∀ t, PlanePeriodic (w t) := translated_periodic (-δ) hvp
  have hs : GlobalTorusScalarSolution 1 (centeredDrift V p detectorBumpDerivativeBound L)
      (centeredSource p detectorBumpDerivativeBound L) w (fun _ => 0) :=
    global_scalar_solution_translated hsv (-δ)
  have ha := translated_smooth (-δ) (detectorDrift_smooth hV' detectorBumpDerivativeBound L)
  have hap := translated_periodic (-δ) (detectorDrift_periodic hp' detectorBumpDerivativeBound L)
  have had : ∀ t x, PlanarHamiltonian.divergence
      (centeredDrift V p detectorBumpDerivativeBound L t) x = 0 := by
    intro t x
    rw [centeredDrift_eq]
    exact detectorDrift_divergence hV hdiv detectorBumpDerivativeBound L t x
  refine ⟨w, hs, hw, fun t x => hnv t (x + -δ), ?_, hsmall, ?_⟩
  · intro t ht
    rw [scalarMass_translated hv' hvp (-δ) t]
    change (∫ x in Icc (0 : Plane) (fun _ => 1), v t x) ≤ _
    rw [he t ht]
    exact hm₀ t ht
  · intro ν hν
    have hsol := triangularVelocity_solution (viscosityDrift_smooth ha ν)
      (viscosityScalar_smooth hw ν) (hs.viscosity hw hν.le)
      (viscosityDrift_periodic hap ν) (fun t => hwp (ν * t))
      (viscosityDrift_divergence ha had ν)
      (fun x => by
        change ν • detectorDrift V' detectorBumpDerivativeBound L (ν * 0) (x + -δ) = 0
        rw [mul_zero, detectorDrift_before V' detectorBumpDerivativeBound L le_rfl, smul_zero])
    refine ⟨hsol, finite_time_classical_unique (by norm_num) hν.le hsol, ?_⟩
    intro E d H hpair
    let E' : Set Plane := {x | x + δ ∈ E}
    have hobs := (hall ν hν).2.2 E' d H hpair
    have horbit (s : ℝ) : Ψ' 0 s ![1 / 4, 1 / 4] = Ψ 0 s p - δ := by
      simp only [Ψ', translateTransition, δ, reference_add_shift]
    constructor
    · rintro ⟨k, hk⟩
      have hk' : Ψ' 0 k ![1 / 4, 1 / 4] ∈ E' := by
        change Ψ' 0 k ![1 / 4, 1 / 4] + δ ∈ E
        rw [horbit, sub_add_cancel]
        exact hk
      obtain ⟨t, ht, x, hx, hh⟩ := hobs.1 ⟨k, hk'⟩
      refine ⟨t, ht, x + δ, hx, ?_⟩
      change 1 / 2 < v (ν * t) (x + δ + -δ)
      rw [add_neg_cancel_right, he _ (mul_nonneg hν.le ht)]
      exact hh
    · intro hfar t ht x hx
      have hf : ∀ s, 0 ≤ s → ∀ y ∈ E',
          2 * d ≤ torusNorm (Ψ' 0 s ![1 / 4, 1 / 4] - y) := by
        intro s hs' y hy
        rw [horbit]
        have hh := hfar s hs' (y + δ) hy
        convert hh using 2
        abel
      have hx' : x + -δ ∈ E' := by
        change x + -δ + δ ∈ E
        simpa only [neg_add_cancel_right] using hx
      have hh := hobs.2 hf t ht (x + -δ) hx'
      change v (ν * t) (x + -δ) < 1 / 2
      rw [he _ (mul_nonneg hν.le ht)]
      exact hh

end ForcedComputation.VelocityDetector.CompactCenter

end

end OAI
