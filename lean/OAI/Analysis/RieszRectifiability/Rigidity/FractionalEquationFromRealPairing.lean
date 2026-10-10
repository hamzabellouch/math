import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.HeightEnergyPairingIdentity
import OAI.Analysis.RieszRectifiability.Kernel.ComplexPairingRealComponents

namespace OAI

/-!
# Fractional equations from real height pairings

Vanishing real pairings for compactly supported mean-zero tests give the complex fractional
equation by separating real and imaginary parts. Weighted tail integrability then extends the
equation to all mean-zero Schwartz tests.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter SchwartzMap

theorem compact_fractional_equation_of_real_pairing (p : ℕ)
    (a : Ambient (p + 1)) (w : Ambient (p + 1) → ℝ) (hwm : Measurable w)
    (hw : ∀ R : ℝ, 0 < R → IntegrableOn w (ball a R) volume)
    (htail : ∀ R : ℝ, 0 < R → IntegrableOn
      (fun y => |w y| * inverseDistancePow (p + 1 + 2) a y) (closedExterior a R) volume)
    (henergy : ∀ R : ℝ, 0 < R → Integrable
      (fun q : Ambient (p + 1) × Ambient (p + 1) => fractionalPairEnergy (p + 1) w q.1 q.2)
      ((volume.restrict (ball a R)).prod (volume.restrict (ball a R))))
    (hreal : ∀ φ : 𝓢(Ambient (p + 1), ℝ), HasCompactSupport φ → (∫ x, φ x) = 0 →
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
        heightPairingOn (p + 1) volume a (ball a R) w φ = 0)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hc : HasCompactSupport g) (hg : (∫ x, g x) = 0) :
    (∫ x, w x • fractionalSchwartzTest p g x) = 0 := by
  let gr : 𝓢(Ambient (p + 1), ℝ) := g.postcompCLM Complex.reCLM
  let gi : 𝓢(Ambient (p + 1), ℝ) := g.postcompCLM Complex.imCLM
  have hcr : HasCompactSupport gr := hc.comp_left (g := Complex.re) rfl
  have hci : HasCompactSupport gi := hc.comp_left (g := Complex.im) rfl
  have hmr : (∫ x, gr x) = 0 := by
    calc
      _ = (∫ x, g x).re := integral_re g.integrable
      _ = 0 := by rw [hg]; rfl
  have hmi : (∫ x, gi x) = 0 := by
    calc
      _ = (∫ x, g x).im := integral_im g.integrable
      _ = 0 := by rw [hg]; rfl
  obtain ⟨Rr, hRr, hr⟩ := hreal gr hcr hmr
  obtain ⟨Ri, hRi, hi⟩ := hreal gi hci hmi
  obtain ⟨H, hH, hball⟩ := hc.isBounded.subset_closedBall_lt 0 a
  have hnear : ∀ x, g x ≠ 0 → dist x a ≤ H := by
    intro x hx
    exact hball (subset_tsupport g hx)
  let R := 2 * H + Rr + Ri + 1
  have hR : 0 < R := by dsimp [R]; linarith
  have hHR : 2 * H ≤ R := by dsimp [R]; linarith
  let ν := (volume : Measure (Ambient (p + 1))).restrict (ball a R)
  let C := (volume (ball (0 : Ambient (p + 1)) 1)).toReal
  have hvol : GlobalUpperGrowth (p + 1) C (volume : Measure (Ambient (p + 1))) :=
    volume_global_upper_growth (p + 1)
  let : IsFiniteMeasure ν :=
    finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C volume hvol a R hR
  have hI := complex_height_interior_integrable_of_energy p C ν
    (globalGrowth_restrict (p + 1) C volume hvol (ball a R)) w hwm (hw R hR) g (henergy R hR)
  have hgnw : Integrable (fun x => ‖g x‖ * w x) ν :=
    (hw R hR).bdd_mul g.continuous.measurable.norm.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa only [norm_norm] using! g.norm_le_seminorm ℝ x)
  have hN : Integrable (complexRenormalizedNormalIntegrand (p + 1) w g a)
      (ν.prod (volume.restrict (ball a R)ᶜ)) := by
    simpa only [closedExterior_eq_compl_ball] using! complex_renormalized_exterior_integrable
      (p + 1) C volume ν hvol w g hwm g.continuous.measurable g.integrable.restrict.norm
      hgnw a H R hH.le hR hHR (Eventually.of_forall hnear) (htail R hR)
  have hz := complex_height_pairing_zero_of_real_equations (p + 1) volume a (ball a R)
    w g hI hN (hr R (by dsimp [R]; linarith)) (hi R (by dsimp [R]; linarith))
  exact (compact_schwartz_height_energy_pairing_identity p a H R hH.le hR hHR
    w hwm (hw R hR) g hg hnear (htail R hR) (henergy R hR)).2.trans hz

theorem schwartz_fractional_equation_of_real_pairing (p : ℕ)
    (a : Ambient (p + 1)) (w : Ambient (p + 1) → ℝ) (hwm : Measurable w)
    (hw : ∀ R : ℝ, 0 < R → IntegrableOn w (ball a R) volume)
    (htail : ∀ R : ℝ, 0 < R → IntegrableOn
      (fun y => |w y| * inverseDistancePow (p + 1 + 2) a y) (closedExterior a R) volume)
    (henergy : ∀ R : ℝ, 0 < R → Integrable
      (fun q : Ambient (p + 1) × Ambient (p + 1) => fractionalPairEnergy (p + 1) w q.1 q.2)
      ((volume.restrict (ball a R)).prod (volume.restrict (ball a R))))
    (hreal : ∀ φ : 𝓢(Ambient (p + 1), ℝ), HasCompactSupport φ → (∫ x, φ x) = 0 →
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
        heightPairingOn (p + 1) volume a (ball a R) w φ = 0)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hg : (∫ x, g x) = 0) :
    (∫ x, w x • fractionalSchwartzTest p g x) = 0 := by
  have hweight : Integrable (fun x => |w x| * polynomialDecay (p + 3) x) volume :=
    polynomial_weight_integrable_from_height_tail (p + 3) volume w hwm a 1 zero_lt_one
      (hw 1 zero_lt_one) (htail 1 zero_lt_one)
  exact height_fractional_test_zero_on_mean_zero_tests p volume w hwm hweight
    (compact_fractional_equation_of_real_pairing p a w hwm hw htail henergy hreal) g hg

end

end RieszRectifiability

end OAI
