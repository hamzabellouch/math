import Mathlib

namespace OAI

namespace CylinderCovering.RadialInducedField

def Statement : Prop :=
  ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F],
  ∀ (a b : F) (α β : ℝ) (w : ℝ → F) (lam : ℝ → ℝ),
    Module.finrank ℝ F = 2 → LinearIndependent ℝ ![a, b] →
    ContDiffOn ℝ 1 w (Set.Icc α β) →
    (∀ t ∈ Set.Ioo α β, HasDerivAt w (lam t • (a + t • b)) t) →
    ∃ e : (ℝ × ℝ) ≃L[ℝ] F,
      (∀ u v : ℝ, e (u, v) = u • a + v • b) ∧
      (∀ ρ t : ℝ, 0 < ρ →
        w ((e.symm (ρ • (a + t • b))).2 / (e.symm (ρ • (a + t • b))).1) = w t) ∧
      ContDiffOn ℝ 1 (fun z : F => w ((e.symm z).2 / (e.symm z).1))
        {z : F | 0 < (e.symm z).1 ∧ (e.symm z).2 / (e.symm z).1 ∈ Set.Ioo α β} ∧
      ∀ z : F, 0 < (e.symm z).1 →
        (e.symm z).2 / (e.symm z).1 ∈ Set.Ioo α β →
        (fderiv ℝ (fun x : F => w ((e.symm x).2 / (e.symm x).1)) z =
          (fderiv ℝ (fun x : F => (e.symm x).2 / (e.symm x).1) z).smulRight
            (lam ((e.symm z).2 / (e.symm z).1) •
              (a + ((e.symm z).2 / (e.symm z).1) • b))) ∧
        (fderiv ℝ (fun x : F => (e.symm x).2 / (e.symm x).1) z)
          (a + ((e.symm z).2 / (e.symm z).1) • b) = 0 ∧
        (fderiv ℝ (fun x : F => w ((e.symm x).2 / (e.symm x).1)) z).comp
          (fderiv ℝ (fun x : F => w ((e.symm x).2 / (e.symm x).1)) z) = 0

end CylinderCovering.RadialInducedField

end OAI
