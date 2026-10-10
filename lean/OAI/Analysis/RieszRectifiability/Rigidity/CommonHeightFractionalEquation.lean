import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.IntrinsicHeightData
import OAI.Analysis.RieszRectifiability.Kernel.LocalHeightData
import OAI.Analysis.RieszRectifiability.Limits.IntrinsicCompactEquation
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalEquationFromRealPairing

namespace OAI

/-!
# The intrinsic fractional equation for a common height

Local square integrability, pair energy, and tail bounds on a coordinate plane pull back along
its affine isometry. Ambient compact-test equations therefore imply the fractional equation
for every intrinsic mean-zero Schwartz test.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function SchwartzMap
open scoped NNReal

theorem common_height_fractional_equation {d : ℕ} (p : ℕ)
    (e : (Fin (p + 1) → ℝ) → Ambient d) (π : Ambient d → Fin (p + 1) → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (a : Ambient d) (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (hplane : e = affinePlaneSection a L)
    (f : Ambient d → ℝ) (hfm : Measurable f)
    (hf : ∀ H, MemLp f 2 ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))
    (henergy : ∀ H, Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) f q.1 q.2)
      (((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))))
    (htail : ∀ R : ℝ, 0 < R → IntegrableOn
      (fun x => |f x| * inverseDistancePow (p + 1 + 2) (e 0) x)
      (closedExterior (e 0) R) (coordinatePlaneMeasure e))
    (hcompact : ∀ (φ : Ambient d → ℝ) (J B : ℝ≥0), HasCompactSupport φ → LipschitzWith J φ →
      (∀ x, |φ x| ≤ (B : ℝ)) → (∫ x, φ x ∂coordinatePlaneMeasure e) = 0 →
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
        heightPairingOn (p + 1) (coordinatePlaneMeasure e) (e 0) (ball (e 0) R) f φ = 0)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hg : (∫ x, g x) = 0) :
    (∫ x, f (a + L x) • fractionalSchwartzTest p g x) = 0 := by
  have he0 : e 0 = a := by rw [hplane]; simp [affinePlaneSection]
  have hνg : GlobalUpperGrowth (p + 1) ((2 * (Q : ℝ)) ^ (p + 1)) (coordinatePlaneMeasure e) := by
    simpa only [Fintype.card_fin] using! coordinatePlaneMeasure_upper_growth e π
      he.continuous.measurable Q hπ hleft
  let := hνg.finite_on_compacts
  have hdata := local_height_data_on_balls (p + 1) e π K Q hπ hleft (coordinatePlaneMeasure e)
    f hf henergy
  apply schwartz_fractional_equation_of_real_pairing p 0 (fun x => f (a + L x))
    (hfm.comp (show Measurable (fun x : Ambient (p + 1) => a + L x) by fun_prop))
    ?_ ?_ ?_ ?_ g hg
  · intro R hR
    let : IsFiniteMeasure ((coordinatePlaneMeasure e).restrict (ball (e 0) R)) :=
      finiteMeasure_restrict_ball_of_globalGrowth (p + 1) ((2 * (Q : ℝ)) ^ (p + 1))
        (coordinatePlaneMeasure e) hνg (e 0) R hR
    have hi : IntegrableOn f (ball (e 0) R) (coordinatePlaneMeasure e) :=
      (hdata R).1.integrable (by norm_num)
    rw [he0, hplane] at hi
    exact height_local_integrable_affine_pullback a L f R hi
  · intro R hR
    have hi := htail R hR
    rw [he0, hplane] at hi
    exact height_tail_integrable_affine_pullback (p + 1 + 2) a L f R hi
  · intro R _
    have hi := (hdata R).2
    rw [he0, hplane] at hi
    exact height_energy_integrable_affine_pullback (p + 1) a L f R hi
  · intro φ hc hφ
    apply intrinsic_compact_schwartz_equation_of_ambient a L f ?_ φ hc hφ
    intro ψ J B hcψ hψ hB _ hmean
    have hm : (∫ x, ψ x ∂coordinatePlaneMeasure e) = 0 := by
      simpa only [hplane] using! hmean
    have hi := hcompact ψ J B hcψ hψ hB hm
    rw [he0, hplane] at hi
    exact hi

end

end RieszRectifiability

end OAI
