import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicSpaceRestrictRestrict

namespace OAI

noncomputable section
namespace VelocityDetection.PeriodicSpace.Jets
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open SpatialCalculus

def ofPeriodicCurve (a : ℕ) {f : ScalarField 2}
    (hf : ContDiff ℝ ∞ (uncurry f)) (hp : ∀ t, FactorsThrough (f t) cover) (t : ℝ) :
    compatibleJets 2 a := ofSmoothPeriodic a (f t)
      (hf.comp (contDiff_const.prodMk contDiff_id)) (hp t)

@[simp] theorem value_ofPeriodicCurve (a : ℕ) {f : ScalarField 2}
    (hf : ContDiff ℝ ∞ (uncurry f)) (hp : ∀ t, FactorsThrough (f t) cover) (t : ℝ) :
    value (ofPeriodicCurve a hf hp t) = f t :=
  value_ofSmoothPeriodic _ _ _ _

theorem continuous_ofPeriodicCurve (a : ℕ) {f : ScalarField 2}
    (hf : ContDiff ℝ ∞ (uncurry f)) (hp : ∀ t, FactorsThrough (f t) cover) :
    Continuous (ofPeriodicCurve a hf hp) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro ⟨k,w⟩
  exact continuous_ofPeriodic_curve (f := fun t => wordPartial w (f t))
    (contDiff_uncurry_wordPartial hf w).continuous
    (fun t => periodic_wordPartial (hf.comp (contDiff_const.prodMk contDiff_id)) (hp t) w)

@[simp] theorem restrict_ofPeriodicCurve {a b : ℕ} (hab : a ≤ b) {f : ScalarField 2}
    (hf : ContDiff ℝ ∞ (uncurry f)) (hp : ∀ t, FactorsThrough (f t) cover) (t : ℝ) :
    restrict hab (ofPeriodicCurve b hf hp t) = ofPeriodicCurve a hf hp t := by
  apply value_injective
  simp only [restrict_value, value_ofPeriodicCurve]

end VelocityDetection.PeriodicSpace.Jets
end

end OAI
