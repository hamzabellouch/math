import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceCollisionGeometry

namespace OAI

/-! # One outgoing collision followed by a fixed angular pair -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem outgoing_pair_lintegral (r : ℝ≥0∞) (hr : r ≠ ⊤) (v w : V)
    {F : V × (Sphere × Sphere) → ℝ≥0∞} (hF : Measurable F) :
    r * (∫⁻ u, (∫⁻ a, F (u,a) ∂sphereProbability.prod sphereProbability) ∂outgoing (v,w)) =
      ∫⁻ q : Sphere × (Sphere × Sphere), r * F (child v w q.1.1,q.2)
        ∂sphereProbability.prod (sphereProbability.prod sphereProbability) := by
  have hu : Measurable (fun n : Sphere => child v w n.1) := by unfold child; fun_prop
  have hm : Measurable (fun q : Sphere × (Sphere × Sphere) => r*F (child v w q.1.1,q.2)) :=
    measurable_const.mul (hF.comp ((hu.comp measurable_fst).prodMk measurable_snd))
  have hi : Measurable (fun u : V => ∫⁻ a, F (u,a) ∂sphereProbability.prod sphereProbability) :=
    hF.lintegral_prod_right'
  rw [outgoing_apply,lintegral_map hi hu,lintegral_prod _ hm.aemeasurable,
    ← lintegral_const_mul' _ _ hr]
  apply lintegral_congr
  intro n
  exact (lintegral_const_mul' _ _ hr).symm

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
