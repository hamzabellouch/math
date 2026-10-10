import OAI.Analysis.ModularRecovery.TomitaFundamental

namespace OAI

/-! The cutoff half-exponential identity on the actual closed Tomita graph.
This is the bounded spectral calculation used before taking modular-weight
limits; it does not assert the existence or traciality of a core weight. -/

noncomputable section
open scoped Topology

namespace BoundedRecovery.RealSpectralCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma halfGraph_multiplier (D : RealSpectralCalculus H) {x y : H}
    (hxy : (x, y) ∈ D.halfGraph) (f g : BoundedContinuousFunction ℝ ℂ)
    (hfg : g * halfResolvent = f * (1 - halfResolvent)) :
    D.calculus f y = D.calculus g x := by
  have hx : D.calculus halfResolvent (x + y) = x :=
    (D.halfGraph_iff_resolvent x y).mp hxy
  have hy : D.calculus (1 - halfResolvent) (x + y) = y := by
    rw [map_sub, map_one, sub_apply, one_apply_eq_self, hx]
    abel
  calc
    D.calculus f y = D.calculus f (D.calculus (1 - halfResolvent) (x + y)) := by rw [hy]
    _ = D.calculus (f * (1 - halfResolvent)) (x + y) := by
      rw [map_mul]
      rfl
    _ = D.calculus (g * halfResolvent) (x + y) := by rw [hfg]
    _ = D.calculus g (D.calculus halfResolvent (x + y)) := by
      rw [map_mul]
      rfl
    _ = D.calculus g x := by rw [hx]

lemma halfGraph_cutoff (D : RealSpectralCalculus H) {x y : H}
    (hxy : (x, y) ∈ D.halfGraph) (f : BoundedContinuousFunction ℝ ℂ) (n : ℕ)
    (hf : ∀ t : ℝ, (n : ℝ) < t → f t = 0) :
    D.calculus f y = D.calculus (f * halfExponentialCutoff n) x := by
  apply D.halfGraph_multiplier hxy
  ext t
  by_cases ht : (n : ℝ) < t
  · simp only [BoundedContinuousFunction.coe_mul, Pi.mul_apply, hf t ht, zero_mul]
  · have htn : min (n : ℝ) t = t := min_eq_right (le_of_not_gt ht)
    have hr : (Real.exp (t / 2) : ℂ) * halfResolvent t = 1 - halfResolvent t := by
      rw [halfResolvent_apply]
      have hrR : Real.exp (t / 2) * (Real.exp (t / 2) + 1)⁻¹ =
          1 - (Real.exp (t / 2) + 1)⁻¹ := by
        field_simp [ne_of_gt (add_pos (Real.exp_pos (t / 2)) zero_lt_one)]
        ring
      exact_mod_cast hrR
    change (f t * (Real.exp (min (n : ℝ) t / 2) : ℂ)) * halfResolvent t =
      f t * (1 - halfResolvent t)
    rw [htn, mul_assoc, hr]

end BoundedRecovery.RealSpectralCalculus

namespace BoundedRecovery.StandardModularData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma cutoff_tomita_vector (S : StandardModularData H) (a : H →L[ℂ] H)
    (ha : a ∈ S.M) (f : BoundedContinuousFunction ℝ ℂ) (n : ℕ)
    (hf : ∀ t : ℝ, (n : ℝ) < t → f t = 0) :
    S.D.calculus f (S.J (star a (S.xi))) =
      S.D.calculus (f * halfExponentialCutoff n) (a S.xi) :=
  S.D.halfGraph_cutoff (S.core_halfGraph a ha) f n hf

end BoundedRecovery.StandardModularData

end

end OAI
